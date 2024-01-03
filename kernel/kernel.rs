pub(crate) struct State {
    defs: Vec<(Rc<str>, Expr)>,
}

pub(crate) mod builtins {
    pub(crate) const LEVEL: Expr = Expr::FVar(0);
    pub(crate) const LEVEL_Z: Expr = Expr::FVar(1);
    pub(crate) const LEVEL_S: Expr = Expr::FVar(2);
    pub(crate) const LEVEL_MAX: Expr = Expr::FVar(3);
    pub(crate) const LEVEL_IMAX: Expr = Expr::FVar(4);
    pub(crate) const SORT: Expr = Expr::FVar(5);
    pub(crate) const BUILTINS: usize = 6;
    use super::*;
}
use builtins::*;

impl State {
    pub fn new(builtin_names: [&str; BUILTINS]) -> Self {
        let builtin_types: [Expr; BUILTINS] = [
            SORT.app([LEVEL_S.app([LEVEL_Z])]),
            LEVEL,
            LEVEL.pi(LEVEL),
            LEVEL.pi(LEVEL).pi(LEVEL),
            LEVEL.pi(LEVEL).pi(LEVEL),
            SORT.app([LEVEL_S.app([Expr::BVar(0)])]).pi(LEVEL),
        ];
        let builtin_names = builtin_names.into_iter().map(<Rc<str>>::from);
        let defs = builtin_names.zip(builtin_types).collect();
        State { defs }
    }
    pub fn add(&mut self, name: &str, r#type: Expr) -> (Rc<str>, u32) {
        let name = <Rc<str>>::from(name);
        self.defs.push((name.clone(), r#type));
        (name, (self.defs.len() - 1).try_into().unwrap())
    }
    pub fn truncate(&mut self, len: u32) -> Result<(), String> {
        if (len as usize) < BUILTINS {
            return Err("cannot truncate builtins".to_owned());
        }
        self.defs.truncate(len as usize);
        Ok(())
    }
    pub fn type_of(&mut self, value: &Expr) -> Result<Expr, String> {
        let st = self;
        let mut bvars = Vec::new();
        let bvars = Stack::new(&mut bvars);
        let depth = &mut 0;
        type_of(&mut Context { st, bvars, depth }, value)
    }
    pub fn name_of(&self, fvar: u32) -> &str {
        &self.defs[fvar as usize].0
    }
}

struct Context<'a> {
    st: &'a mut State,
    bvars: Stack<'a, &'a Expr>,
    depth: &'a mut u32,
}

fn type_of(cx: &mut Context<'_>, expr: &Expr) -> Result<Expr, String> {
    log::trace!("{:4} type_of({})", cx.display(expr), cx.depth);
    *cx.depth += 1;
    let res = match expr {
        &Expr::FVar(fvar) => cx.st.defs[fvar as usize].1.clone(),
        &Expr::BVar(n) => {
            let mut ty = cx.bvars[cx.bvars.len() - 1 - usize::from(n)].clone();
            (ty.raise(0, n + 1), ty).1
        }
        Expr::Sortω(l) => Expr::Sortω(l.checked_add(1).ok_or("Sortω overflow")?),
        Expr::Lam(l, r) => bind(cx, l, |cx, _| Ok(type_of(cx, r)?.pi(l.clone())))?,
        Expr::Pi(l, r) => bind(cx, l, |cx, l_univ| {
            Ok(match (l_univ, type_of(cx, r)?.expect_univ(cx)?) {
                (Univ::Sort(l), Univ::Sort(mut r)) => match r.lower(0, 1) {
                    Ok(()) => SORT.app([LEVEL_IMAX.app([l, r])]),
                    Err(()) => Expr::Sortω(0),
                },
                (Univ::Sortω(a), Univ::Sort(_)) => Expr::Sortω(a),
                (Univ::Sort(_), Univ::Sortω(a)) => Expr::Sortω(a),
                (Univ::Sortω(a), Univ::Sortω(b)) => Expr::Sortω(Ord::max(a, b)),
            })
        })?,
        Expr::App(l, r) => {
            let mut l_type = type_of(cx, l)?;
            make_whnf(&mut l_type);
            let Expr::Pi(mut f_in, mut f_out) = l_type else {
                let (l, l_type) = (cx.display(l), cx.display(&l_type));
                return Err(format!("application LHS `{l} : {l_type}` not Π type"));
            };
            let mut r_type = type_of(cx, r)?;
            ensure_def_eq(cx, &mut f_in, &mut r_type)?;
            (f_out.subst(r), *f_out).1
        }
    };
    *cx.depth -= 1;
    log::trace!("{:4} type_of result: {}", cx.depth, cx.display(&res));
    Ok(res)
}

fn bind<R, F>(cx: &mut Context<'_>, expr: &Expr, f: F) -> Result<R, String>
where
    F: FnOnce(&mut Context<'_>, Univ) -> Result<R, String>,
{
    let univ = type_of(cx, expr)?.expect_univ(cx)?;
    let (st, depth) = (&mut *cx.st, &mut *cx.depth);
    cx.bvars.reborrow().with(expr, move |bvars| {
        let mut cx = Context { st, bvars, depth };
        f(&mut cx, univ)
    })
}

fn ensure_def_eq(cx: &mut Context<'_>, lhs: &mut Expr, rhs: &mut Expr) -> Result<(), String> {
    if !def_eq(cx, lhs, rhs) {
        let (l, r) = (cx.display(lhs), cx.display(rhs));
        return Err(format!("type mismatch:\nexpected {l}\n   found {r}"));
    }
    Ok(())
}

fn def_eq(cx: &mut Context<'_>, lhs: &mut Expr, rhs: &mut Expr) -> bool {
    let (l, r) = (cx.display(lhs), cx.display(rhs));
    log::trace!("{:4} def_eq({l}, {r})", cx.depth);
    *cx.depth += 1;

    make_whnf(lhs);
    make_whnf(rhs);

    let res = (match (&mut *lhs, &mut *rhs) {
        (Expr::FVar(a), Expr::FVar(b)) => a == b,
        (Expr::BVar(n), Expr::BVar(m)) => n == m,
        (Expr::Sortω(n), Expr::Sortω(m)) => n == m,
        (Expr::Pi(a, b), Expr::Pi(c, d)) => {
            def_eq(cx, a, c) && bind(cx, a, |cx, _| Ok(def_eq(cx, b, d))).unwrap()
        }
        (Expr::Lam(a, b), Expr::Lam(c, d)) => {
            def_eq(cx, a, c) && bind(cx, a, |cx, _| Ok(def_eq(cx, b, d))).unwrap()
        }
        (Expr::App(a, b), Expr::App(c, d)) => def_eq(cx, a, c) && def_eq(cx, b, d),
        _ => false,
    }) || level::def_eq(cx, lhs, rhs).unwrap_or(false)
        || uip(cx, lhs, rhs);

    *cx.depth -= 1;
    log::trace!("{:4} def_eq result: {res}", cx.depth);
    res
}

// TODO: This is inefficient…
fn uip(cx: &mut Context<'_>, lhs: &mut Expr, rhs: &mut Expr) -> bool {
    let not_proof = |e: &Expr| matches!(*e, LEVEL_Z) || e.is_app(&LEVEL_S);
    let _ = (not_proof(lhs) || not_proof(rhs)) && return false;

    let mut lhs_sort = type_of(cx, lhs).unwrap();
    if let Univ::Sort(mut level) = type_of(cx, &lhs_sort).unwrap().into_univ().unwrap() {
        if def_eq(cx, &mut level, &mut LEVEL_Z) {
            let mut rhs_sort = type_of(cx, rhs).unwrap();
            let _ = def_eq(cx, &mut lhs_sort, &mut rhs_sort) && return true;
        }
    }
    false
}

mod level {
    pub(super) fn def_eq(cx: &mut Context<'_>, lhs: &mut Expr, rhs: &mut Expr) -> Result<bool, ()> {
        let _ = (!is(lhs) && !is(rhs)) && return Err(());
        let exprs = Vec::new();
        let mut vars = Vars { cx, exprs };
        let lhs_term = term(&mut vars, lhs)?;
        let rhs_term = term(&mut vars, rhs)?;
        let (mut l, mut r) = Default::default();
        max(&mut l, &lhs_term)?;
        max(&mut r, &rhs_term)?;

        let vars = vars.exprs.len() as u8;
        log::trace!("{} → {l:?}", cx.display(lhs));
        log::trace!("{} → {r:?}", cx.display(rhs));
        let eq = (0..(1_u16 << vars))
            .all(|s| apply(&l, vars, s).is_some_and(|l| Some(l) == apply(&r, vars, s)));
        log::trace!("result: {eq}");
        Ok(eq)
    }
    fn is(e: &Expr) -> bool {
        *e == LEVEL_Z
            || e.is_app(&LEVEL_S)
            || matches!(e, Expr::App(e, _) if e.is_app(&LEVEL_MAX) || e.is_app(&LEVEL_IMAX))
    }
    enum Term {
        Var(u8),
        Zero,
        Succ(Box<Term>),
        Max(Box<Term>, Box<Term>),
        IMax(Box<Term>, Box<Term>),
    }
    struct Vars<'a, 'b, 'e> {
        cx: &'a mut Context<'b>,
        exprs: Vec<&'e mut Expr>,
    }
    fn term<'e>(vars: &mut Vars<'_, '_, 'e>, e: &'e mut Expr) -> Result<Box<Term>, ()> {
        make_whnf(e);
        Ok(Box::new(match e {
            &mut LEVEL_Z => Term::Zero,
            _ if e.is_app(&LEVEL_S) => Term::Succ(term(vars, e.unwrap_app().1)?),
            Expr::App(f, _) if f.is_app(&LEVEL_MAX) => {
                let (f, b) = e.unwrap_app();
                Term::Max(term(vars, f.unwrap_app().1)?, term(vars, b)?)
            }
            Expr::App(f, _) if f.is_app(&LEVEL_IMAX) => {
                let (f, b) = e.unwrap_app();
                Term::IMax(term(vars, f.unwrap_app().1)?, term(vars, b)?)
            }
            _ => Term::Var(match vars
                .exprs
                .iter_mut()
                .position(|ex| super::def_eq(vars.cx, ex, e))
            {
                Some(i) => i,
                None if vars.exprs.len() == 16 => return Err(()),
                None => (vars.exprs.push(e), vars.exprs.len() - 1).1,
            } as u8),
        }))
    }
    type Normalized = Vec<(u16, Vec<(u8, u16)>)>;
    fn max(n: &mut Normalized, t: &Term) -> Result<(), ()> {
        match t {
            &Term::Var(v) => n.push((0, vec![(v, 0)])),
            Term::Zero => n.push((0, Vec::new())),
            Term::Succ(t) => {
                let old_len = n.len();
                max(n, t)?;
                for (k, imax_adds) in &mut n[old_len..] {
                    let k = imax_adds.last_mut().map(|(_, k)| k).unwrap_or(k);
                    *k = k.checked_add(1).ok_or(())?;
                }
            }
            Term::Max(a, b) => (max(n, a)?, max(n, b)?).1,
            Term::IMax(a, b) => imax(n, a, b)?,
        }
        Ok(())
    }
    fn imax(n: &mut Normalized, a: &Term, b: &Term) -> Result<(), ()> {
        match b {
            &Term::Var(b) => {
                let old_len = n.len();
                max(n, a)?;
                n[old_len..].iter_mut().for_each(|(_, v)| v.push((b, 0)));
            }
            Term::Zero => n.push((0, Vec::new())),
            Term::Succ(_) => (max(n, a)?, max(n, b)?).1,
            Term::Max(b, c) => (imax(n, a, b)?, imax(n, a, c)?).1,
            Term::IMax(b, c) => (imax(n, a, c)?, imax(n, b, c)?).1,
        }
        Ok(())
    }
    fn apply(n: &Normalized, vars: u8, states: u16) -> Option<(u16, Vec<u16>)> {
        let mut offsets = vec![0; usize::from(vars)];
        let mut iter = n.iter().map(|&(base, ref imax_adds)| {
            let mut total = 1_u16;
            #[allow(clippy::never_loop, unused_must_use)]
            for &(imax_with, add) in imax_adds.iter().rev() {
                total = total.checked_add(add)?;
                states & (1 << imax_with) == 0 && return Some(total - 1);
                offsets[imax_with as usize] = offsets[imax_with as usize].max(total);
            }
            (total - 1).checked_add(base)
        });
        let k = iter.try_fold(0, |acc, i| Some(acc.max(i?)))?;
        let result = (k.max(*offsets.iter().max().unwrap_or(&0)), offsets);
        log::trace!("{states:16b} → {result:?}");
        Some(result)
    }

    use super::*;
}

fn make_whnf(e: &mut Expr) {
    while let Expr::App(l, r) = e {
        make_whnf(l);
        match &mut **l {
            Expr::Lam(_, body) => (body.subst(r), *e = take(body)).1,
            _ => break,
        }
    }
}

impl Expr {
    fn subst_with<F: FnMut(&mut Expr)>(&mut self, mut subst: F) {
        self.visit(0, |old, e| match e {
            Self::BVar(n) if old == *n => (subst(e), e.raise(0, old)).1,
            Self::BVar(n) if old < *n => *n -= 1,
            _ => {}
        });
    }
    fn subst(&mut self, new: &Expr) {
        self.subst_with(|e| e.clone_from(new));
    }
    fn raise(&mut self, depth: u16, by: u16) {
        self.visit(depth, |depth, e| match e {
            Self::BVar(n) if depth <= *n => *n += by,
            _ => {}
        })
    }
    fn lower(&mut self, depth: u16, by: u16) -> Result<(), ()> {
        self.try_visit(depth, &mut |depth, e| {
            match e {
                &mut Self::BVar(n) if depth <= n && n < depth + by => return Err(()),
                Self::BVar(n) if depth + by <= *n => *n -= by,
                _ => {}
            }
            Ok(())
        })
    }
    fn into_univ(self) -> Result<Univ, Self> {
        Ok(match self {
            Expr::App(l, r) if *l == SORT => Univ::Sort(r),
            Expr::Sortω(n) => Univ::Sortω(n),
            _ => return Err(self),
        })
    }
    fn expect_univ(self, cx: &Context<'_>) -> Result<Univ, String> {
        self.into_univ()
            .map_err(|e| format!("expression `{}` not a sort", cx.display(&e)))
    }
}
#[derive(Debug)]
enum Univ {
    Sort(Box<Expr>),
    Sortω(u16),
}

impl<'c> Context<'c> {
    fn display<'a>(&'a self, e: &'a Expr) -> DisplayExpr<'a, 'c> {
        DisplayExpr(self, e)
    }
}
struct DisplayExpr<'a, 'c>(&'a Context<'c>, &'a Expr);
impl Display for DisplayExpr<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.1 {
            &Expr::FVar(n) => f.write_str(self.0.st.name_of(n)),
            Expr::BVar(n) => write!(f, "_{n}"),
            Expr::Sortω(n) => write!(f, "Sortω{}", Sub(*n)),
            Expr::Lam(l, r) | Expr::Pi(l, r) => {
                let (l_, r) = (Self(self.0, l), Self(self.0, r));
                let s = match &self.1 {
                    Expr::Lam(..) => "λ",
                    _ => "∀",
                };
                match &**l {
                    Expr::Pi(..) | Expr::App(..) => write!(f, "{s} _: ({l_}), {r}"),
                    _ => write!(f, "{s} _: {l_}, {r}"),
                }
            }
            Expr::App(l, r) => {
                match &**l {
                    Expr::Lam(..) => write!(f, "({}) ", Self(self.0, l))?,
                    _ => write!(f, "{} ", Self(self.0, l))?,
                }
                match &**r {
                    Expr::App(..) => write!(f, "({})", Self(self.0, r)),
                    _ => write!(f, "{}", Self(self.0, r)),
                }
            }
        }
    }
}

struct Sub(u16);
impl Display for Sub {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0 != 0 {
            Display::fmt(&Self(self.0 / 10), f)?;
            write!(f, "{}", self.0 % 10)?;
        }
        Ok(())
    }
}

use crate::expr::Expr;
use crate::stack::Stack;
use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;
use std::mem::take;
use std::rc::Rc;
