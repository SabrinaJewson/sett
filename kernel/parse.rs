pub(crate) struct State {
    kernel: kernel::State,
    defs: HashMap<String, u32>,
}

impl State {
    pub fn new() -> Self {
        let defs = HashMap::new();
        let builtins = [
            "Level",
            "Level:0",
            "Level:s",
            "Level:max",
            "Level:imax",
            "Sort",
        ];
        let kernel = kernel::State::new(builtins);
        let mut this = Self { defs, kernel };
        for (i, name) in builtins.iter().enumerate() {
            this.def(name, i as u32).unwrap();
        }
        this
    }
    pub fn parse(&mut self, input: &str) -> Result<(), String> {
        let mut input = input.trim_start_matches(['\n', '\t', ' ']);
        let mut transparent = Vec::new();
        while !input.is_empty() {
            if peek(input) == Some(["remove"]) {
                exact_token(&mut input, "remove")?;
                let n = fvar(&self.defs, token(&mut input).ok_or("unexpected EOF")?)?;
                self.kernel.truncate(n)?;
                for i in n..self.defs.len() as u32 {
                    self.defs.remove(self.kernel.name_of(i));
                }
                continue;
            }
            transparent.clear();
            let transparent_start = self.defs.len() as u32;
            loop {
                exact_token(&mut input, "def")?;
                let ident = token(&mut input).ok_or("unexpected EOF")?;
                let ident = ident.strip_suffix(':').ok_or("no trailing colon")?;
                let r#type = self.expr(&mut input)?;
                exact_token(&mut input, ":=")?;

                let value = self.expr(&mut input)?;
                let mut checker = LEVEL_Z.lam(r#type.clone()).app([value]);
                checker.visit_mut(0, |_, e| match e {
                    &mut Expr::FVar(n) if transparent_start <= n => {
                        e.clone_from(&transparent[(n - transparent_start) as usize]);
                    }
                    _ => {}
                });
                self.kernel.type_of(&checker)?;
                transparent.push(take(checker.unwrap_app().1));

                self.constant(ident, r#type)?;

                if peek(input) != Some([","]) {
                    break;
                }
                exact_token(&mut input, ",")?;
            }
            exact_token(&mut input, ";")?;
        }
        Ok(())
    }
    pub fn axiom(&mut self, ident: &str, r#type: &str) -> Result<(), String> {
        let (e, _) = self.check_expr(r#type)?;
        self.constant(ident, e)?;
        Ok(())
    }
    pub(crate) fn check_expr(&mut self, mut expr: &str) -> Result<(Expr, Expr), String> {
        let e = self.expr(&mut expr)?;
        if !expr.is_empty() {
            return Err("trailing tokens in axiom".to_owned());
        }
        let r#type = self.kernel.type_of(&e)?;
        Ok((e, r#type))
    }
    fn constant(&mut self, ident: &str, r#type: Expr) -> Result<(), String> {
        let n = self.kernel.add(ident, r#type);
        self.def(ident, n)
    }
    fn def(&mut self, ident: &str, fvar: u32) -> Result<(), String> {
        if self.defs.contains_key(ident) {
            return Err(format!("duplicate definition `{ident}`"));
        }
        log::info!("added decl {ident} = {fvar}");
        self.defs.insert(ident.to_owned(), fvar);
        Ok(())
    }
    fn expr(&self, input: &mut &str) -> Result<Expr, String> {
        let defs = &self.defs;
        let locals = Vec::new();
        expr(&mut Context { defs, locals }, input)
    }
}

struct Context<'s, 'i> {
    defs: &'s HashMap<String, u32>,
    locals: Vec<&'i str>,
}

fn expr<'i>(cx: &mut Context<'_, 'i>, input: &mut &'i str) -> Result<Expr, String> {
    let mut acc: Option<Expr> = None;
    loop {
        let expr = match token(input).ok_or("unexpected EOF")? {
            i if i.starts_with("Sortω") => Expr::Sortω(number("Sortω", i)?),
            "∀" => bind(cx, input, |cx, input, l| {
                exact_token(input, ",")?;
                Ok(expr(cx, input)?.pi(l))
            })?,
            "λ" => bind(cx, input, |cx, input, l| {
                exact_token(input, ",")?;
                Ok(expr(cx, input)?.lam(l))
            })?,
            "Ind" => Expr::Ind(ind(cx, input)?),
            i if i.starts_with("Ind:constr") => {
                Expr::IndConstr(number("Ind:constr", i)?, ind(cx, input)?)
            }
            "Ind:elim" => Expr::IndElim(ind(cx, input)?),
            "(" => (expr(cx, input)?, exact_token(input, ")")?).0,
            ")" => return Err("unexpected `)`; expected expression".to_owned()),
            v => match cx.locals.iter().rev().position(|&x| x == v) {
                Some(i) => Expr::BVar(i as u16),
                None => Expr::FVar(fvar(cx.defs, v)?),
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

fn fvar(defs: &HashMap<String, u32>, v: &str) -> Result<u32, String> {
    let res = defs.get(v).copied();
    res.ok_or_else(|| format!("unknown variable `{v}`"))
}

fn ind<'i>(cx: &mut Context<'_, 'i>, input: &mut &'i str) -> Result<Box<Ind>, String> {
    exact_token(input, "(")?;
    let sm = peek(input) == Some(["small", ","]);
    if sm {
        exact_token(input, "small").unwrap();
        exact_token(input, ",").unwrap();
    }
    bind(cx, input, |cx, input, arity| {
        let mut constrs = Vec::new();
        while input.starts_with(',') {
            exact_token(input, ",").unwrap();
            constrs.push(expr(cx, input)?);
        }
        exact_token(input, ")")?;
        Ok(Box::new(Ind { sm, arity, constrs }))
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

fn number(prefix: &str, input: &str) -> Result<u16, String> {
    let input = input.strip_prefix(prefix).unwrap();
    input.chars().try_fold(0_u16, |a, v| {
        let v = u32::from(v).wrapping_sub(u32::from('₀'));
        if 10 <= v {
            return Err(format!("unexpected digit {v}"));
        }
        let a = a.checked_mul(10).and_then(|a| a.checked_add(v as u16));
        a.ok_or_else(|| "number too large".to_owned())
    })
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

use crate::expr::Expr;
use crate::expr::Ind;
use crate::kernel;
use crate::kernel::builtins::*;
use std::collections::HashMap;
use std::mem::take;
