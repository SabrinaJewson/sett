pub(crate) struct State<'s> {
    pub kernel: kernel::State,
    defs: HashMap<&'s str, Expr>,
}

impl<'s> State<'s> {
    pub fn new() -> Self {
        let mut defs = HashMap::new();
        defs.insert("Level", kernel::LEVEL);
        defs.insert("Level:0", kernel::LEVEL_Z);
        defs.insert("Level:s", kernel::LEVEL_S);
        defs.insert("Level:max", kernel::LEVEL_MAX);
        defs.insert("Level:imax", kernel::LEVEL_IMAX);
        defs.insert("Sort", kernel::SORT);
        let kernel = kernel::State::new();
        Self { defs, kernel }
    }
    pub fn alias(&mut self, ident: &'s str, e: Expr) -> Result<(), String> {
        if self.defs.contains_key(ident) {
            return Err(format!("duplicate definition `{ident}`"));
        }
        log::info!("added decl {ident} = {e:?}");
        self.defs.insert(ident, e);
        Ok(())
    }
    pub fn parse(&mut self, input: &'s str) -> Result<(), String> {
        let mut input = input.trim_start_matches(['\n', '\t', ' ']);
        while !input.is_empty() {
            exact_token(&mut input, "def")?;
            let ident = token(&mut input).ok_or("unexpected EOF")?;
            exact_token(&mut input, ":=")?;
            let value = self.expr(&mut input)?;
            let r#type = self.type_check(&value)?;
            let n = self.kernel.add(r#type, Some(value.clone()));
            self.alias(ident, Expr::FVar(n))?;

            if peek(input) == Some([","]) {
                exact_token(&mut input, ",")?;
                exact_token(&mut input, "with")?;
                let ident = token(&mut input).ok_or("unexpected EOF")?;
                let ident = ident.strip_suffix(':').ok_or("no trailing colon")?;
                let r#type = self.expr(&mut input)?;
                exact_token(&mut input, ":=")?;
                let proof = self.expr(&mut input)?;

                let mut checker = Expr::BVar(0).bind(Lam, r#type.clone()).app([proof]);
                checker.visit_mut(0, |_, e| match e {
                    &mut Expr::FVar(m) if n == m => e.clone_from(&value),
                    _ => {}
                });
                self.type_check(&checker)?;

                let n = self.kernel.add(r#type, None);
                self.alias(ident, Expr::FVar(n))?;
            }
            exact_token(&mut input, ";")?;
        }
        Ok(())
    }
    pub fn whole_expr(&self, input: &str) -> Result<Expr, String> {
        let mut input = input.trim_start_matches(['\n', '\t', ' ']);
        let e = self.expr(&mut input)?;
        if !input.is_empty() {
            return Err("trailing tokens".to_owned());
        }
        Ok(e)
    }
    pub fn type_check(&mut self, expr: &Expr) -> Result<Expr, String> {
        if kernel::logging_enabled() {
            let mut names = vec![String::new(); self.defs.len()];
            for (k, v) in &self.defs {
                match v {
                    &Expr::FVar(n) => names[n as usize] = (*k).to_owned(),
                    _ => unreachable!(),
                }
            }
            crate::expr::FVAR_NAMES.set(Some(names));
        }
        self.kernel.type_check(expr)
    }
    fn expr(&self, input: &mut &str) -> Result<Expr, String> {
        let defs = &self.defs;
        let locals = Vec::new();
        expr(&mut Context { defs, locals }, input)
    }
}

struct Context<'s, 'i> {
    defs: &'s HashMap<&'s str, Expr>,
    locals: Vec<&'i str>,
}

fn expr<'i>(cx: &mut Context<'_, 'i>, input: &mut &'i str) -> Result<Expr, String> {
    let mut acc: Option<Expr> = None;
    loop {
        let expr = match token(input).ok_or("unexpected EOF")? {
            "Sortω" => Expr::Sortω(number(input)?),
            kind @ ("λ" | "Π" | "∀") => {
                let kind = if kind == "λ" { Lam } else { Pi };
                bind(cx, input, |cx, input, l| {
                    exact_token(input, ",")?;
                    Ok(expr(cx, input)?.bind(kind, l))
                })?
            }
            "Ind" => Expr::Ind(ind(cx, input)?),
            "Ind:constr" => Expr::IndConstr(number(input)?, ind(cx, input)?),
            "Ind:elim" => Expr::IndElim(ind(cx, input)?),
            "(" => (expr(cx, input)?, exact_token(input, ")")?).0,
            ")" => return Err("unexpected `)`; expected expression".to_owned()),
            v => match cx.locals.iter().rev().position(|&x| x == v) {
                Some(i) => Expr::BVar(i as u16),
                None => {
                    let val = cx.defs.get(v).cloned();
                    val.ok_or_else(|| format!("unknown variable `{v}`"))?
                }
            },
        };
        let new_acc = match acc {
            Some(acc) => acc.app([expr]),
            None => expr,
        };
        if matches!(peek(input), Some([")" | "," | ";" | ":="]) | None) {
            break Ok(new_acc);
        }
        acc = Some(new_acc);
    }
}

fn ind<'i>(cx: &mut Context<'_, 'i>, input: &mut &'i str) -> Result<Ind, String> {
    exact_token(input, "(")?;
    let sm = peek(input) == Some(["small", ","]);
    if sm {
        exact_token(input, "small").unwrap();
        exact_token(input, ",").unwrap();
    }
    bind(cx, input, |cx, input, arity| {
        let arity = Box::new(arity);
        let mut constrs = Vec::new();
        while input.starts_with(',') {
            exact_token(input, ",").unwrap();
            constrs.push(expr(cx, input)?);
        }
        exact_token(input, ")")?;
        Ok(Ind { sm, arity, constrs })
    })
}

fn bind<'s, 'i, F, R>(cx: &mut Context<'s, 'i>, input: &mut &'i str, f: F) -> Result<R, String>
where
    F: FnOnce(&mut Context<'s, 'i>, &mut &'i str, Expr) -> Result<R, String>,
{
    let ident = token(input).ok_or("unexpected EOF")?;
    let ident = ident.strip_suffix(':').ok_or("no trailing colon")?;
    let l = expr(cx, input)?;
    if cx.locals.len() == usize::from(u16::MAX) {
        return Err("too many binders".to_owned());
    }
    cx.locals.push(ident);
    let r = f(cx, input, l)?;
    cx.locals.pop();
    Ok(r)
}

fn number(input: &mut &str) -> Result<u16, String> {
    let n = token(input).ok_or("unexpected EOF")?;
    n.parse::<u16>().map_err(|_| format!("not a number: `{n}`"))
}

fn exact_token(input: &mut &str, expected: &str) -> Result<(), String> {
    match token(input).ok_or("unexpected EOF")? {
        t if t == expected => Ok(()),
        t => Err(format!("unexpected token `{t}`; expected `{expected}`")),
    }
}

fn peek<const N: usize>(mut input: &str) -> Option<[&str; N]> {
    let mut array = [""; N];
    for t in &mut array {
        *t = token(&mut input)?;
    }
    Some(array)
}

fn token<'s>(input: &mut &'s str) -> Option<&'s str> {
    let punct = ['(', ')', ',', ';', '\n', '\t', ' '];
    if input.is_empty() {
        return None;
    }
    let res;
    (res, *input) = input.split_at(match input.find(punct).unwrap_or(input.len()) {
        0 => input.chars().next().unwrap().len_utf8(),
        n => n,
    });
    *input = input.trim_start_matches(['\n', '\t', ' ']);
    Some(res)
}

use crate::expr::Bind::*;
use crate::expr::Expr;
use crate::expr::Ind;
use crate::kernel;
use std::collections::HashMap;
