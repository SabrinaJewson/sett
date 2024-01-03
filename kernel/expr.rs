#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expr {
    FVar(u32),
    BVar(u16),
    Sortω(u16),
    Lam(Box<Expr>, Box<Expr>),
    Pi(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

impl Default for Expr {
    fn default() -> Self {
        Self::Sortω(37)
    }
}

impl Expr {
    pub fn try_visit<E, F>(&mut self, depth: u16, f: &mut F) -> Result<(), E>
    where
        F: FnMut(u16, &mut Expr) -> Result<(), E>,
    {
        match self {
            Self::Lam(l, r) | Self::Pi(l, r) => {
                (l.try_visit(depth, f)?, r.try_visit(depth + 1, f)?).1
            }
            Self::App(l, r) => (l.try_visit(depth, f)?, r.try_visit(depth, f)?).1,
            _ => {}
        }
        f(depth, self)
    }
}

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
    pub fn visit(&mut self, depth: u16, mut f: impl FnMut(u16, &mut Expr)) {
        let _ = self.try_visit(depth, &mut |depth, e| {
            f(depth, e);
            Ok::<_, Infallible>(())
        });
    }
}

use std::convert::Infallible;
