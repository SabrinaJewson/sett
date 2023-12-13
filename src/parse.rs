pub(crate) fn parse<'s>(st: &mut State<'s>, input: &'s str) -> Result<(), String> {
    let mut input = input.trim_start_matches(['\n', '\t', ' ']);
    while !input.is_empty() {
        exact_token(&mut input, "def")?;
        let ident = token(&mut input).ok_or("unexpected EOF")?;
        exact_token(&mut input, ":=")?;
        let value = expr(&mut Vec::new(), &mut input)?;
        let r#type = kernel::check(st, &value)?;
        st.defs.insert(ident, (r#type, Some(value.clone())));
        exact_token(&mut input, "with")?;
        let eq = token(&mut input).ok_or("unexpected EOF")?;
        if eq != "_" {
            let axiom = Expr::fvar_app("Eq", [Expr::FVar(ident), value]);
            st.defs.insert(eq, (axiom, None));
        }
        log::debug!("added decl {ident}");
    }
    Ok(())
}

pub(crate) fn whole_expr(input: &str) -> Result<Expr<'_>, String> {
    let mut input = input.trim_start_matches(['\n', '\t', ' ']);
    let e = expr(&mut Vec::new(), &mut input)?;
    if !input.is_empty() {
        return Err("trailing tokens".to_owned());
    }
    Ok(e)
}

fn expr<'s>(cx: &mut Vec<&'s str>, input: &mut &'s str) -> Result<Expr<'s>, String> {
    let mut acc = None;
    loop {
        let expr = match token(input).ok_or("unexpected EOF")? {
            "Sortω" => Expr::Sortω(number(input)?),
            kind @ ("λ" | "Π" | "∀") => {
                let kind = if kind == "λ" { Lam } else { Pi };
                bind(cx, input, |cx, input, l| {
                    exact_token(input, ",")?;
                    Ok(Expr::Bind(kind, Box::new(l), Box::new(expr(cx, input)?)))
                })?
            }
            "Ind" => Expr::Ind(ind(cx, input)?),
            "Ind:constr" => Expr::IndConstr(number(input)?, ind(cx, input)?),
            "Ind:elim" => Expr::IndElim(ind(cx, input)?),
            "Ind:iota" => Expr::IndIota(number(input)?, ind(cx, input)?),
            "(" => (expr(cx, input)?, exact_token(input, ")")?).0,
            ")" => return Err("unexpected `)`; expected expression".to_owned()),
            v => match cx.iter().rev().position(|&x| x == v) {
                Some(i) => Expr::BVar(i as u16),
                None => Expr::FVar(v),
            },
        };
        let new_acc = match acc {
            Some(acc) => Expr::App(Box::new(acc), Box::new(expr)),
            None => expr,
        };
        if input.is_empty() || input.starts_with([')', ',']) || input.starts_with("with ") {
            break Ok(new_acc);
        }
        acc = Some(new_acc);
    }
}

fn ind<'s>(cx: &mut Vec<&'s str>, input: &mut &'s str) -> Result<Ind<'s>, String> {
    exact_token(input, "(")?;
    bind(cx, input, |cx, input, arity| {
        let arity = Box::new(arity);
        let mut constrs = Vec::new();
        while input.starts_with(',') {
            exact_token(input, ",").unwrap();
            constrs.push(expr(cx, input)?);
        }
        exact_token(input, ")")?;
        Ok(Ind { arity, constrs })
    })
}

fn bind<'s, F, R>(cx: &mut Vec<&'s str>, input: &mut &'s str, f: F) -> Result<R, String>
where
    F: FnOnce(&mut Vec<&'s str>, &mut &'s str, Expr<'s>) -> Result<R, String>,
{
    let ident = token(input).ok_or("unexpected EOF")?;
    let ident = ident.strip_suffix(':').ok_or("no trailing colon")?;
    let l = expr(cx, input)?;
    if cx.len() == usize::from(u16::MAX) {
        return Err("too many binders".to_owned());
    }
    cx.push(ident);
    let r = f(cx, input, l)?;
    cx.pop();
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

fn token<'s>(input: &mut &'s str) -> Option<&'s str> {
    let punct = ['(', ')', ',', '\n', '\t', ' '];
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
use crate::expr::State;
use crate::kernel;
