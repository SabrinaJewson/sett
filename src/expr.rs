#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Expr {
    FVar(u32),
    BVar(u16),
    Sortω(u16),
    Lam(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Ind(Ind),
    IndConstr(u16, Ind),
    IndElim(Ind),
}

impl Default for Expr {
    fn default() -> Self {
        Self::Sortω(37)
    }
}

thread_local! {
    pub(crate) static FVAR_NAMES: RefCell<Option<Vec<String>>> = RefCell::new(None);
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            &Self::FVar(n) => FVAR_NAMES.with_borrow(|fvars| match fvars {
                Some(fvars) => write!(f, "{}", fvars[n as usize]),
                None => write!(f, "{n}"),
            }),
            Self::BVar(n) => write!(f, "_{n}"),
            Self::Sortω(n) => write!(f, "Sortω {n}"),
            Self::Lam(l, r) => match &**l {
                Self::Pi(_, _) | Self::App(_, _) => write!(f, "λ _: ({l:?}), {r:?}"),
                _ => write!(f, "λ _: {l:?}, {r:?}"),
            },
            Self::Pi(l, r) => match &**l {
                Self::Pi(_, _) | Self::App(_, _) => write!(f, "∀ _: ({l:?}), {r:?}"),
                _ => write!(f, "∀ _: {l:?}, {r:?}"),
            },
            Self::App(l, r) => {
                match &**l {
                    Self::Lam(_, _) => write!(f, "({l:?}) ")?,
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
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Ind {
    pub sm: bool,
    pub arity: Box<Expr>,
    pub constrs: Vec<Expr>,
}

impl Debug for Ind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.sm {
            false => write!(f, "(_: {:?}", self.arity)?,
            true => write!(f, "(small, _: {:?}", self.arity)?,
        }
        for c in &self.constrs {
            write!(f, ", {c:?}")?;
        }
        f.write_str(")")
    }
}

macro_rules! visit {
    ($($ident:ident $($mut:ident)?),*) => { $(
        impl Expr {
            pub fn $ident<E, F>(&$($mut)? self, depth: u16, f: &mut F) -> Result<(), E>
            where
                F: FnMut(u16, &$($mut)? Expr) -> Result<(), E>,
            {
                match self {
                    Expr::Lam(l, r) | Expr::Pi(l, r) => (l.$ident(depth, f)?, r.$ident(depth + 1, f)?).1,
                    Expr::App(l, r) => (l.$ident(depth, f)?, r.$ident(depth, f)?).1,
                    Expr::Ind(i) | Expr::IndConstr(_, i) | Expr::IndElim(i) => i.$ident(depth, f)?,
                    _ => {}
                }
                f(depth, self)
            }
        }
        impl Ind {
            pub fn $ident<E, F>(&$($mut)? self, depth: u16, f: &mut F) -> Result<(), E>
            where
                F: FnMut(u16, &$($mut)? Expr) -> Result<(), E>,
            {
                self.arity.$ident(depth, f)?;
                (&$($mut)? self.constrs).into_iter().try_for_each(|c| c.$ident(depth + 1, f))
            }
        }
    )* }
}
visit!(try_visit, try_visit_mut mut);

impl Expr {
    pub fn lam(self, r#type: impl Into<Box<Expr>>) -> Self {
        Self::Lam(r#type.into(), Box::new(self))
    }
    pub fn pi(self, r#type: impl Into<Box<Expr>>) -> Self {
        Self::Pi(r#type.into(), Box::new(self))
    }
    pub fn app<T: Into<Box<Expr>>>(self, args: impl IntoIterator<Item = T>) -> Self {
        args.into_iter()
            .fold(self, |e, a| Expr::App(Box::new(e), a.into()))
    }
    pub fn is_app(&self, applicand: &Expr) -> bool {
        matches!(self, Self::App(f, _) if **f == *applicand)
    }
    pub fn unwrap_app(&mut self) -> (&mut Expr, &mut Expr) {
        match self {
            Self::App(a, b) => (a, b),
            _ => panic!(),
        }
    }
    pub fn visit_mut(&mut self, depth: u16, mut f: impl FnMut(u16, &mut Expr)) {
        let _ = self.try_visit_mut(depth, &mut |depth, e| {
            f(depth, e);
            Ok::<_, Infallible>(())
        });
    }
}

use std::cell::RefCell;
use std::convert::Infallible;
use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;
