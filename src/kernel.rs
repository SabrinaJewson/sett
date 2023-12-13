pub(crate) fn check<'s>(st: &mut State<'s>, expr: &Expr<'s>) -> Result<Expr<'s>, String> {
    let mut bvars = Vec::new();
    let bvars = Stack::new(&mut bvars);
    let depth = 0;
    let mut cx = Context { st, bvars, depth };
    type_of(&mut cx, expr)
}

struct Context<'a, 's> {
    st: &'a mut State<'s>,
    bvars: Stack<'a, &'a Expr<'s>>,
    depth: u32,
}

impl<'s> Context<'_, 's> {
    fn reborrow(&mut self) -> Context<'_, 's> {
        let st = &mut *self.st;
        let bvars = self.bvars.reborrow();
        let depth = self.depth;
        Context { st, bvars, depth }
    }
}

fn type_of<'s>(cx: &mut Context<'_, 's>, expr: &Expr<'s>) -> Result<Expr<'s>, String> {
    log::trace!("{:4} type_of({expr:?})", cx.depth);
    cx.depth += 1;
    let res = match expr {
        Expr::FVar(ident) => {
            let def = cx.st.defs.get(ident);
            let def = def.ok_or_else(|| format!("unknown fvar `{ident}`"))?;
            def.0.clone()
        }
        &Expr::BVar(n) => {
            let mut ty = cx.bvars[cx.bvars.len() - 1 - usize::from(n)].clone();
            (ty.raise(0, n + 1), ty).1
        }
        Expr::Sortω(l) => Expr::Sortω(l.checked_add(1).ok_or("levelω overflow")?),
        Expr::Bind(Lam, l, r) => bind(cx, l, |cx, _| {
            Ok(Expr::Bind(Pi, l.clone(), Box::new(type_of(cx, r)?)))
        })?,
        Expr::Bind(Pi, l, r) => bind(cx, l, |cx, l_sort| {
            Ok(match (l_sort, type_of(cx, r)?.expect_sort()?) {
                (Sort::Sort(l), Sort::Sort(r)) => {
                    // TODO: `r` thrown away…
                    if let Some(r) = r.lower(0, 1) {
                        let level = Expr::fvar_app("Level:imax", [l, Box::new(r)]);
                        Sort::Sort(Box::new(level)).into_expr()
                    } else {
                        Expr::Sortω(0)
                    }
                }
                (Sort::Sortω(a), Sort::Sort(_)) => Expr::Sortω(a),
                (Sort::Sort(_), Sort::Sortω(a)) => Expr::Sortω(a),
                (Sort::Sortω(a), Sort::Sortω(b)) => Expr::Sortω(Ord::max(a, b)),
            })
        })?,
        Expr::App(l, r) => match whnf(type_of(cx, l)?) {
            Expr::Bind(Pi, mut f_in, mut f_out) => {
                let mut r_type = type_of(cx, r)?;
                ensure_def_eq(cx, &mut f_in, &mut r_type)?;
                (f_out.subst(0, r), *f_out).1
            }
            t => return Err(format!("application LHS `{l:?} : {t:?}` not Π type")),
        },
        Expr::Ind(i) => (ind_check(cx, i)?, (*i.arity).clone()).1,
        &Expr::IndConstr(n, ref i) => {
            ind_check(cx, i)?;
            let c = i.constrs.get(usize::from(n)).cloned();
            let mut c = c.ok_or_else(|| format!("only {} constructors", i.constrs.len()))?;
            (c.subst_with(0, &mut |e| *e = Expr::Ind(i.clone())), c).1
        }
        Expr::IndElim(i) => {
            let large_elim = ind_check(cx, i)?;
            let constrs = i.constrs.len() as u16;
            let mut t = i.arity.clone();
            t.raise(0, 1 + constrs);
            telescope_map(&mut t, 0, |e, d| {
                let major_premise = Expr::Ind(i.clone()).app_n((0..d).rev().map(Expr::BVar));
                let out = Expr::BVar(1 + d + constrs).app_n((0..=d).rev().map(Expr::BVar));
                *e = Expr::Bind(Pi, Box::new(major_premise), Box::new(out));
            });
            for (k, c) in i.constrs.iter().enumerate() {
                let mut minor_premise = c.clone();
                telescope_map(&mut minor_premise, 0, |recs, max_d| {
                    let constr = Expr::IndConstr(k as u16, i.clone());
                    *recs = minor_premise_recs(k as u16, c, constr, max_d, 0, 0)
                });
                t = Box::new(Expr::Bind(Pi, Box::new(minor_premise), t));
            }
            let mut motive_type = i.arity.clone();
            telescope_map(&mut motive_type, 0, |e, d| {
                let v = Expr::Ind(i.clone()).app_n((0..d).rev().map(Expr::BVar));
                let rhs = Sort::Sort(Box::new(match large_elim {
                    true => Expr::FVar("Level:0"),
                    false => Expr::BVar(1 + d),
                }));
                *e = Expr::Bind(Pi, Box::new(v), Box::new(rhs.into_expr()));
            });
            let mut t = Expr::Bind(Pi, motive_type, t);
            if large_elim {
                t = Expr::Bind(Pi, Box::new(Expr::FVar("Level")), Box::new(t));
            }
            t
        }
        &Expr::IndIota(_n, ref i) => {
            let _large_elim = ind_check(cx, i)?;
            todo!()
        }
    };
    cx.depth -= 1;
    log::trace!("{:4} type_of result: {res:?}", cx.depth);
    Ok(res)
}

fn ind_check<'s>(cx: &mut Context<'_, 's>, ind: &Ind<'s>) -> Result<bool, String> {
    let mut base_sort = arity(cx, &ind.arity, 0)?;
    let level_kind = level::kind(cx, &mut base_sort).ok_or("invalid sort for inductive type")?;
    let mut large_elim = true;

    let mut base_sort = Sort::Sort(Box::new(base_sort)).into_expr();
    base_sort.raise(0, 1);
    let num_constrs = u16::try_from(ind.constrs.len()).map_err(|_| "too many constructors")?;
    bind(cx, &ind.arity, |cx, _| {
        for c in &ind.constrs {
            let mut sort = type_of(cx, c)?;
            ensure_def_eq(cx, &mut base_sort, &mut sort)?;

            let mut arg_level = constr(cx, c, 0)?;
            match level_kind {
                level::Kind::AlwaysZero => {
                    large_elim =
                        num_constrs == 1 && def_eq(cx, &mut arg_level, &mut Expr::FVar("Level:0"))
                }
                level::Kind::SometimesZero if 1 < ind.constrs.len() => {
                    return Err(">1 constructor for potentially-zero sort".to_owned())
                }
                level::Kind::SometimesZero => {
                    let level = sort.into_finite_sort().unwrap();
                    let mut level = Expr::fvar_app("Level:max", [arg_level, level]);
                    let base_level = base_sort.as_finite_sort_mut().unwrap();
                    ensure_def_eq(cx, base_level, &mut level)?;
                }
                level::Kind::AlwaysNonzero => {}
            }
        }
        Ok(())
    })?;

    Ok(large_elim)
}

fn minor_premise_recs<'s>(
    i: u16,
    c: &Expr<'s>,
    mut constr: Expr<'s>,
    max_d: u16,
    d: u16,
    rec: u16,
) -> Expr<'s> {
    match c {
        Expr::BVar(_) | Expr::App(_, _) => {
            assert_eq!(d, max_d);
            let mut c = c.clone();
            c.raise(d, i);
            c.raise(0, rec);
            constr.raise(0, 1 + i + d + rec);
            c.app_n([constr.app_n((rec..rec + d).rev().map(Expr::BVar))])
        }
        Expr::Bind(Pi, l, c) if l.has_bvar(d) => {
            let mut l = l.clone();
            l.raise(d, i);
            l.raise(0, rec + max_d - d);
            telescope_map(&mut l, 0, |e, args| {
                let a = Expr::BVar(args + rec + max_d - 1 - d);
                let a = a.app_n((0..args).rev().map(Expr::BVar));
                *e = take(e).app_n([a]);
            });
            let r = minor_premise_recs(i, c, constr, max_d, d + 1, rec + 1);
            Expr::Bind(Pi, l, Box::new(r))
        }
        Expr::Bind(Pi, _, c) => minor_premise_recs(i, c, constr, max_d, d + 1, rec),
        _ => unreachable!("not a constructor type: {c:?}"),
    }
}

fn arity<'s>(cx: &mut Context<'_, 's>, a: &Expr<'s>, d: u16) -> Result<Expr<'s>, String> {
    if let Some(e) = a.as_finite_sort() {
        let msg = "universe level cannot depend on indices";
        Ok(e.lower(0, d).ok_or(msg)?)
    } else if let Expr::Bind(Pi, l, r) = a {
        bind(cx, l, |cx, _| arity(cx, r, d + 1))
    } else {
        Err(format!("{a:?} not a valid arity"))
    }
}

fn bind<'s, R, F>(cx: &mut Context<'_, 's>, expr: &Expr<'s>, f: F) -> Result<R, String>
where
    F: FnOnce(&mut Context<'_, 's>, Sort<'s>) -> Result<R, String>,
{
    let sort = type_of(cx, expr)?.expect_sort()?;
    let (st, depth) = (&mut *cx.st, cx.depth);
    cx.bvars.reborrow().with(expr, move |bvars| {
        let mut cx = Context { st, bvars, depth };
        f(&mut cx, sort)
    })
}

fn ensure_def_eq<'s>(
    cx: &mut Context<'_, 's>,
    lhs: &mut Expr<'s>,
    rhs: &mut Expr<'s>,
) -> Result<(), String> {
    if !def_eq(cx, lhs, rhs) {
        return Err(format!("type mismatch: expected {lhs:?}, got {rhs:?}"));
    }
    Ok(())
}

fn def_eq<'s>(cx: &mut Context<'_, 's>, lhs: &mut Expr<'s>, rhs: &mut Expr<'s>) -> bool {
    log::trace!("{:4} def_eq({lhs:?}, {rhs:?})", cx.depth);
    cx.depth += 1;

    make_whnf(lhs);
    make_whnf(rhs);

    let r = (match (&mut *lhs, &mut *rhs) {
        (Expr::FVar(a), Expr::FVar(b)) => a == b,
        (Expr::BVar(n), Expr::BVar(m)) => n == m,
        (Expr::Sortω(n), Expr::Sortω(m)) => n == m,
        (Expr::Bind(a, b, c), Expr::Bind(d, e, f)) => {
            a == d && def_eq(cx, b, e) && bind(cx, b, |cx, _| Ok(def_eq(cx, c, f))).unwrap()
        }
        (Expr::App(a, b), Expr::App(c, d)) => def_eq(cx, a, c) && def_eq(cx, b, d),
        (Expr::Ind(a), Expr::Ind(b)) => ind_def_eq(cx, a, b),
        (Expr::IndConstr(n, a), Expr::IndConstr(m, b)) => n == m && ind_def_eq(cx, a, b),
        (Expr::IndElim(a), Expr::IndElim(b)) => ind_def_eq(cx, a, b),
        _ => false,
    }) || level::def_eq(cx, lhs, rhs).unwrap_or(false)
        || uip(cx, lhs, rhs);

    cx.depth -= 1;
    log::trace!("{:4} def_eq result: {r}", cx.depth);

    r
}

fn ind_def_eq<'s>(cx: &mut Context<'_, 's>, lhs: &mut Ind<'s>, rhs: &mut Ind<'s>) -> bool {
    lhs.constrs.len() == rhs.constrs.len() && def_eq(cx, &mut lhs.arity, &mut rhs.arity) && {
        let mut iter = lhs.constrs.iter_mut().zip(&mut rhs.constrs);
        iter.all(|(l, r)| def_eq(cx, l, r))
    }
}

// TODO: This is inefficient…
fn uip<'s>(cx: &mut Context<'_, 's>, lhs: &mut Expr<'s>, rhs: &mut Expr<'s>) -> bool {
    let not_proof = |e: &Expr<'_>| {
        e.is_fvar_app("Sort") || matches!(e, Expr::Sortω(_) | Expr::Bind(Pi, ..) | Expr::Ind(_))
    };
    let not_prop =
        |e: &Expr<'_>| e.is_fvar("Level") || e.is_fvar_app("Sort") || matches!(e, Expr::Sortω(_));
    if !not_proof(lhs) && !not_proof(rhs) {
        let l = type_of(cx, lhs).unwrap();
        let r = type_of(cx, rhs).unwrap();
        #[allow(unused_must_use)]
        if !not_prop(&l) && !not_prop(&r) {
            let mut l = type_of(cx, &l).unwrap();
            let mut r = type_of(cx, &r).unwrap();
            let mut zero = Expr::fvar_app("Sort", [Expr::FVar("Level:0")]);
            def_eq(cx, &mut l, &mut zero) && def_eq(cx, &mut r, &mut zero) && return true;
        }
    }
    false
}

mod level {
    #[allow(unused_must_use)]
    pub(super) fn def_eq<'s>(
        cx: &mut Context<'_, 's>,
        lhs: &mut Expr<'s>,
        rhs: &mut Expr<'s>,
    ) -> Result<bool, ()> {
        (!is(lhs) && !is(rhs)) && return Err(());
        let exprs = Vec::new();
        let cx = &mut cx.reborrow();
        let mut vars = Vars { cx, exprs };
        let lhs_term = term(&mut vars, lhs)?;
        let rhs_term = term(&mut vars, rhs)?;
        let (mut l, mut r) = Default::default();
        max(&mut l, &lhs_term)?;
        max(&mut r, &rhs_term)?;

        let vars = vars.exprs.len() as u8;
        Ok((0..(1_u16 << vars))
            .all(|s| apply(&l, vars, s).is_some_and(|l| Some(l) == apply(&r, vars, s))))
    }
    fn is(e: &Expr<'_>) -> bool {
        e.is_fvar("Level:0")
            || e.is_fvar_app("Level:s")
            || matches!(e, Expr::App(f, _) if f.is_fvar_app("Level:max") || f.is_fvar_app("Level:imax"))
    }
    pub(super) enum Kind {
        AlwaysZero,
        SometimesZero,
        AlwaysNonzero,
    }
    pub(super) fn kind<'s>(cx: &mut Context<'_, 's>, e: &mut Expr<'s>) -> Option<Kind> {
        match e {
            Expr::FVar("Level:zero") => return Some(Kind::AlwaysZero),
            Expr::App(f, _) if f.is_fvar("Level:s") => return Some(Kind::AlwaysNonzero),
            Expr::BVar(_) => return Some(Kind::SometimesZero),
            _ => {}
        }

        let exprs = Vec::new();
        let cx = &mut cx.reborrow();
        let mut vars = Vars { cx, exprs };
        let mut n = Normalized::default();
        max(&mut n, &*term(&mut vars, e).ok()?).ok()?;
        let mut possible = [false; 2];
        for s in 0..(1 << vars.exprs.len()) {
            let (k, vals) = apply(&n, vars.exprs.len() as u8, s)?;
            possible[(k != 0 || vals.iter().any(|v| *v != 0)) as usize] = true;
        }
        Some(match possible {
            [true, false] => Kind::AlwaysZero,
            [true, true] => Kind::SometimesZero,
            [false, true] => Kind::AlwaysNonzero,
            [false, false] => unreachable!(),
        })
    }
    enum Term {
        Var(u8),
        Zero,
        Succ(Box<Term>),
        Max(Box<Term>, Box<Term>),
        IMax(Box<Term>, Box<Term>),
    }
    struct Vars<'e, 's> {
        cx: &'e mut Context<'e, 's>,
        exprs: Vec<&'e mut Expr<'s>>,
    }
    fn term<'e, 's>(vars: &mut Vars<'e, 's>, e: &'e mut Expr<'s>) -> Result<Box<Term>, ()> {
        make_whnf(e);
        Ok(Box::new(match e {
            Expr::FVar("Level:0") => Term::Zero,
            _ if e.is_fvar_app("Level:s") => Term::Succ(term(vars, e.unwrap_app().1)?),
            Expr::App(f, _) if f.is_fvar_app("Level:max") => {
                let (f, b) = e.unwrap_app();
                Term::Max(term(vars, f.unwrap_app().1)?, term(vars, b)?)
            }
            Expr::App(f, _) if f.is_fvar_app("Level:imax") => {
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
                states & (1 << imax_with) == 0 && return Some(0);
                total = total.checked_add(add)?;
                offsets[imax_with as usize] = offsets[imax_with as usize].max(total);
            }
            (total - 1).checked_add(base)
        });
        let k = iter.try_fold(0, |acc, i| Some(acc.max(i?)))?;
        Some((k.max(*offsets.iter().max().unwrap_or(&0)), offsets))
    }

    use super::*;
}

fn make_whnf(e: &mut Expr<'_>) {
    while let Expr::App(f, arg) = e {
        make_whnf(f);
        match &mut **f {
            Expr::Bind(Lam, _, body) => (body.subst(0, arg), *e = take(body)).1,
            _ => break,
        }
    }
}
fn whnf(mut e: Expr<'_>) -> Expr<'_> {
    (make_whnf(&mut e), e).1
}

fn constr<'s>(cx: &mut Context<'_, 's>, c: &Expr<'s>, d: u16) -> Result<Expr<'s>, String> {
    Ok(match c {
        &Expr::BVar(v) if v == d => Expr::FVar("Level:0"),
        Expr::App(_, r) if r.has_bvar(d) => return Err("invalid constructor".to_owned()),
        Expr::App(l, _) => constr(cx, l, d)?,
        Expr::Bind(Pi, l, r) => {
            let msg = "depended-on parameter cannot reference type";
            match l.has_bvar(d) {
                true if r.has_bvar(0) => return Err(msg.to_owned()),
                true => strict_positive(l, d)?,
                false => {}
            }
            bind(cx, l, |cx, left_sort| {
                // TODO: Thrown away
                let left_level = left_sort.into_finite().unwrap().lower(0, d).unwrap();
                let rec = constr(cx, r, d + 1)?;
                Ok(Expr::fvar_app("Level:max", [left_level, rec]))
            })
            .unwrap()
        }
        _ => return Err(format!("invalid expression in constructor: `{c:?}`")),
    })
}

fn strict_positive(e: &Expr<'_>, depth: u16) -> Result<(), String> {
    match e {
        &Expr::BVar(v) if v == depth => Ok(()),
        Expr::App(_, r) if r.has_bvar(depth) => Err("not strict positive".to_owned()),
        Expr::App(l, _) => strict_positive(l, depth),
        Expr::Bind(Pi, l, r) => {
            if l.has_bvar(depth) {
                return Err("not strict positive".to_owned());
            }
            strict_positive(r, depth + 1)
        }
        _ => Err(format!("not strict positive: `{e:?}`")),
    }
}

fn telescope_map<'s, R>(e: &mut Expr<'s>, d: u16, f: impl FnOnce(&mut Expr<'s>, u16) -> R) -> R {
    match e {
        Expr::Bind(Pi, _, r) => telescope_map(&mut *r, d + 1, f),
        _ => f(e, d),
    }
}

impl<'s> Expr<'s> {
    fn has_bvar(&self, n: u16) -> bool {
        match self {
            &Self::BVar(m) if n == m => true,
            Self::Bind(_, l, r) => l.has_bvar(n) || r.has_bvar(n + 1),
            Self::App(l, r) => l.has_bvar(n) || r.has_bvar(n),
            Self::Ind(i) | Self::IndConstr(_, i) | Self::IndElim(i) | Self::IndIota(_, i) => {
                i.has_bvar(n)
            }
            Self::FVar(_) | Self::BVar(_) | Self::Sortω(_) => false,
        }
    }
    fn subst_with<F: ?Sized + FnMut(&mut Expr<'s>)>(&mut self, old: u16, new: &mut F) {
        match self {
            Self::BVar(n) if *n == old => (new(self), self.raise(0, old)).1,
            Self::BVar(n) if *n > old => *n -= 1,
            Self::Bind(_, l, r) => (l.subst_with(old, new), r.subst_with(old + 1, new)).0,
            Self::App(l, r) => (l.subst_with(old, new), r.subst_with(old, new)).0,
            Self::Ind(i) | Self::IndConstr(_, i) | Self::IndElim(i) | Self::IndIota(_, i) => {
                i.subst_with(old, new)
            }
            Self::FVar(_) | Self::BVar(_) | Self::Sortω(_) => {}
        }
    }
    fn subst(&mut self, old: u16, new: &Expr<'s>) {
        self.subst_with(old, &mut |e| e.clone_from(new));
    }
    fn raise(&mut self, depth: u16, by: u16) {
        match self {
            Self::BVar(n) if *n >= depth => *n += by,
            Self::Bind(_, l, r) => (l.raise(depth, by), r.raise(depth + 1, by)).1,
            Self::App(l, r) => (l.raise(depth, by), r.raise(depth, by)).1,
            Self::Ind(i) | Self::IndConstr(_, i) | Self::IndElim(i) | Self::IndIota(_, i) => {
                i.raise(depth, by)
            }
            Self::FVar(_) | Self::BVar(_) | Self::Sortω(_) => {}
        }
    }
    fn lower(&self, depth: u16, by: u16) -> Option<Self> {
        Some(match self {
            &Self::BVar(n) if depth <= n && n < depth + by => return None,
            &Self::BVar(n) if depth + by <= n => Self::BVar(n - by),
            &Self::Bind(b, ref l, ref r) => {
                let (l, r) = (l.lower(depth, by)?, r.lower(depth + 1, by)?);
                Self::Bind(b, Box::new(l), Box::new(r))
            }
            Self::App(l, r) => l.lower(depth, by)?.app_n([r.lower(depth, by)?]),
            Self::Ind(i) => Self::Ind(i.lower(depth, by)?),
            &Self::IndConstr(n, ref i) => Self::IndConstr(n, i.lower(depth, by)?),
            Self::IndElim(i) => Self::IndElim(i.lower(depth, by)?),
            &Self::IndIota(n, ref i) => Self::IndIota(n, i.lower(depth, by)?),
            Self::FVar(_) | Self::BVar(_) | Self::Sortω(_) => self.clone(),
        })
    }
}

impl<'s> Ind<'s> {
    fn has_bvar(&self, n: u16) -> bool {
        self.arity.has_bvar(n) || self.constrs.iter().any(|c| c.has_bvar(n + 1))
    }
    fn subst_with<F: ?Sized + FnMut(&mut Expr<'s>)>(&mut self, old: u16, new: &mut F) {
        self.arity.subst_with(old, new);
        self.constrs
            .iter_mut()
            .for_each(|c| c.subst_with(old + 1, new));
    }
    fn raise(&mut self, depth: u16, by: u16) {
        self.arity.raise(depth, by);
        self.constrs.iter_mut().for_each(|c| c.raise(depth + 1, by));
    }
    fn lower(&self, depth: u16, by: u16) -> Option<Self> {
        let arity = Box::new(self.arity.lower(depth, by)?);
        let constrs = self.constrs.iter().map(|c| c.lower(depth + 1, by));
        let constrs = constrs.collect::<Option<_>>()?;
        Some(Self { arity, constrs })
    }
}

impl<'s> Expr<'s> {
    fn into_sort(self) -> Result<Sort<'s>, Self> {
        Ok(match self {
            Expr::App(l, r) if l.is_fvar("Sort") => Sort::Sort(r),
            Expr::Sortω(n) => Sort::Sortω(n),
            _ => return Err(self),
        })
    }
    fn into_finite_sort(self) -> Result<Expr<'s>, Self> {
        match self {
            Expr::App(l, r) if l.is_fvar("Sort") => Ok(*r),
            _ => Err(self),
        }
    }
    fn as_finite_sort(&self) -> Option<&Expr<'s>> {
        Some(match self {
            Expr::App(l, r) if l.is_fvar("Sort") => r,
            _ => return None,
        })
    }
    fn as_finite_sort_mut(&mut self) -> Option<&mut Expr<'s>> {
        Some(match self {
            Expr::App(l, r) if l.is_fvar("Sort") => r,
            _ => return None,
        })
    }
    fn expect_sort(self) -> Result<Sort<'s>, String> {
        self.into_sort()
            .map_err(|e| format!("expression `{e:?}` not a sort"))
    }
}
#[derive(Debug)]
enum Sort<'s> {
    Sort(Box<Expr<'s>>),
    Sortω(u16),
}
impl<'s> Sort<'s> {
    fn into_finite(self) -> Result<Expr<'s>, Self> {
        match self {
            Self::Sort(level) => Ok(*level),
            Sort::Sortω(_) => Err(self),
        }
    }
    fn into_expr(self) -> Expr<'s> {
        match self {
            Self::Sort(e) => Expr::fvar_app("Sort", [e]),
            Self::Sortω(n) => Expr::Sortω(n),
        }
    }
}

use crate::expr::Bind::*;
use crate::expr::Expr;
use crate::expr::Ind;
use crate::expr::State;
use crate::stack::Stack;
use std::mem::take;
