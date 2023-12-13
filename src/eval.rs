pub(crate) fn new_state() -> State<'static> {
    let defs = HashMap::new();
    let mut st = State { defs };
    for (name, r#type) in BUILTINS {
        let r#type = match parse::whole_expr(r#type) {
            Ok(r#type) => r#type,
            Err(e) => panic!("invalid builtin {name} of type `{type}` : {e}"),
        };
        st.defs.insert(name, (r#type, None));
    }
    if let Err(e) = parse::parse(&mut st, PRELUDE) {
        panic!("invalid prelude: {e}");
    }
    st
}

pub(crate) fn eval<'s>(st: &mut State<'s>, s: &'s str) -> Result<(), String> {
    let expr = parse::whole_expr(s)?;
    let id = parse::whole_expr("λ x: MetaM (PUnit (Sort (Level:s Level:0))), x").unwrap();
    let expr = Expr::App(Box::new(id), Box::new(expr));
    kernel::check(st, &expr)?;
    Ok(())
}

#[rustfmt::skip]
const BUILTINS: &[(&str, &str)] = &[
    ("Level", "Sort (Level:s Level:0)"),
    ("Level:0", "Level"),
    ("Level:s", "∀ u: Level, Level"),
    ("Level:max", "∀ u: Level, ∀ v: Level, Level"),
    ("Level:imax", "∀ u: Level, ∀ v: Level, Level"),
    ("Sort", "∀ l: Level, Sort (Level:s l)"),
    ("MetaM", "∀ α: Sort (Level:s Level:0), Sort (Level:s Level:0)"),
    //("print", "
    //("read_file", "∀ path:"),
];

const PRELUDE: &str = "
    def Eq := λ u: Level, λ α: Sort u, Ind (
        Self: ∀ a: α, ∀ b: α, Sort Level:0,
        ∀ a: α, Self a a
    )
    with Eq:eq_ind

    def PUnit := λ u: Level, Ind (Self: Sort u, Self)
    with PUnit:eq_ind

    def id := λ u: Level, λ α: Sort u, λ a: α, a
    with id:def
    def id_check := λ u: Level, id (Level:imax (Level:s u) u) (∀ α: Sort u, ∀ x: α, α) (id u)
    with _

    def imp_trans := λ A: Sort Level:0, λ B: Sort Level:0, λ C: Sort Level:0,
        λ h₁: ∀ h: A, B, λ h₂: ∀ h: B, C, λ h: A, h₂ (h₁ h)
    with _

    def imp_trans_check := id (Level:0)
        (∀ A: Sort Level:0, ∀ B: Sort Level:0, ∀ C: Sort Level:0, ∀ h₁: ∀ h: A, B, ∀ h₂: ∀ h: B, C, ∀ h: A, C)
        imp_trans
    with _

    def ↔ := λ u: Level, λ v: Level, λ α: Sort u, λ β: Sort v,
        Ind(Self: Sort (Level:max u v), ∀ to: ∀ a: α, β, ∀ of: ∀ b: β, α,
            ∀ of_to: ∀ a: α, Eq u α (of (to a)) a, ∀ to_of: ∀ b: β, Eq v β (to (of b)) b, Self)
    with ↔:eq_ind
";

use crate::expr::Expr;
use crate::expr::State;
use crate::kernel;
use crate::parse;
use std::collections::HashMap;
