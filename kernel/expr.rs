#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expr {
    FVar(u32),
    BVar(u16),
    Sortω(u16),
    Lam(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Ind(Box<Ind>),
    IndConstr(u16, Box<Ind>),
    IndElim(Box<Ind>),
}

impl Default for Expr {
    fn default() -> Self {
        Self::Sortω(37)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Ind {
    pub sm: bool,
    pub arity: Expr,
    pub constrs: Vec<Expr>,
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

use std::convert::Infallible;
