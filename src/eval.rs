pub(crate) struct State {
    parse: parse::State<'static>,
    meta_m_unit: Expr,
}

impl State {
    pub fn new() -> Self {
        let mut parse = parse::State::new();
        let builtins = &[(
            "MetaM",
            "∀ α: Sort (Level:s Level:0), Sort (Level:s Level:0)",
        )];
        for (name, r#type) in builtins {
            let r#type = parse.whole_expr(r#type).unwrap();
            let n = parse.kernel.add(r#type, None);
            parse.alias(name, Expr::FVar(n)).unwrap();
        }
        parse.parse(PRELUDE).expect("invalid prelude");
        let meta_m_unit = parse
            .whole_expr("MetaM (PUnit (Sort (Level:s Level:0)))")
            .unwrap();
        Self { parse, meta_m_unit }
    }
    pub fn eval(&mut self, s: &str) -> Result<(), String> {
        let e = self.parse.whole_expr(s)?;
        let e = Expr::BVar(0).bind(Lam, self.meta_m_unit.clone()).app([e]);
        self.parse.kernel.type_check(&e).unwrap();
        Ok(())
    }
}

const PRELUDE: &str = "
    def Eq := λ u: Level, λ α: Sort u, Ind (Self: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Self a a),
    with Eq:def: ∀ u: Level,
        (λ α: Sort (Level:s u), Ind (Self: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Self a a))
        (∀ α: Sort u, ∀ a: α, ∀ b: α, Sort Level:0)
        (Eq u)
        (λ α: Sort u, Ind (Self: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Self a a))
        := λ u: Level,
            (λ α: Sort (Level:s u), Ind:constr 0 (Self: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Self a a))
            (∀ α: Sort u, ∀ a: α, ∀ b: α, Sort Level:0)
            (Eq u);
    ";
/*

    def PUnit := λ u: Level, Ind (Self: Sort u, Self)
    with PUnit:eq_ind;

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
    */

use crate::expr::Bind::*;
use crate::expr::Expr;
use crate::parse;
