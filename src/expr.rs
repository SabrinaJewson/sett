pub(crate) struct State<'s> {
    pub defs: HashMap<&'s str, (Expr<'s>, Option<Expr<'s>>)>,
}

#[derive(Clone)]
pub(crate) enum Expr<'s> {
    FVar(&'s str),
    BVar(u16),
    Sortω(u16),
    Bind(Bind, Box<Expr<'s>>, Box<Expr<'s>>),
    App(Box<Expr<'s>>, Box<Expr<'s>>),
    Ind(Ind<'s>),
    IndConstr(u16, Ind<'s>),
    IndElim(Ind<'s>),
    IndIota(u16, Ind<'s>),
}

impl Default for Expr<'_> {
    fn default() -> Self {
        Self::Sortω(37)
    }
}

impl Debug for Expr<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::FVar(x) => f.write_str(x),
            Self::BVar(n) => write!(f, "_{n}"),
            Self::Sortω(n) => write!(f, "Sortω {n}"),
            Self::Bind(Bind::Pi, l, r) => write!(f, "Π _: {l:?}, {r:?}"),
            Self::Bind(Bind::Lam, l, r) => write!(f, "λ _: {l:?}, {r:?}"),
            Self::App(l, r) => {
                match &**l {
                    Self::Bind(_, _, _) => write!(f, "({l:?}) ")?,
                    _ => write!(f, "{l:?} ")?,
                }
                match &**r {
                    Self::App(_, _) => write!(f, "({r:?})"),
                    _ => write!(f, "{r:?}"),
                }
            }
            Self::Ind(i) => write!(f, "Ind {i:?}"),
            Self::IndConstr(n, i) => write!(f, "Ind:constr {n} {i:?}"),
            Self::IndElim(i) => write!(f, "Ind:elim {i:?}"),
            Self::IndIota(n, i) => write!(f, "Ind:iota {n} {i:?}"),
        }
    }
}

impl<'s> Expr<'s> {
    pub fn app_n<I: IntoIterator<Item = T>, T: Into<Box<Expr<'s>>>>(self, args: I) -> Self {
        args.into_iter()
            .fold(self, |e, a| Expr::App(Box::new(e), a.into()))
    }
    pub fn fvar_app<T>(fvar: &'s str, args: impl IntoIterator<Item = T>) -> Self
    where
        T: Into<Box<Expr<'s>>>,
    {
        Self::FVar(fvar).app_n(args)
    }
    pub fn is_fvar(&self, v: &str) -> bool {
        matches!(self, Self::FVar(fvar) if *fvar == v)
    }
    pub fn is_fvar_app(&self, v: &str) -> bool {
        matches!(self, Self::App(f, _) if f.is_fvar(v))
    }
    pub fn unwrap_app(&mut self) -> (&mut Expr<'s>, &mut Expr<'s>) {
        match self {
            Self::App(a, b) => (a, b),
            _ => panic!(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Bind {
    Pi,
    Lam,
}

#[derive(Clone)]
pub(crate) struct Ind<'s> {
    pub arity: Box<Expr<'s>>,
    pub constrs: Vec<Expr<'s>>,
}

impl Debug for Ind<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(_: {:?}", self.arity)?;
        for c in &self.constrs {
            write!(f, ", {c:?}")?;
        }
        f.write_str(")")
    }
}

use std::collections::HashMap;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
