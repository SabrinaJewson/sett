#![allow(
    clippy::short_circuit_statement,
    clippy::diverging_sub_expression,
    const_item_mutation,
    clippy::single_match,
    clippy::new_without_default
)]

pub struct Kernel(parse::State);

impl Kernel {
    pub fn new() -> Self {
        let mut parse = parse::State::new();
        parse.parse(PRELUDE).expect("invalid prelude");
        for (name, r#type) in AXIOMS {
            parse.axiom(name, r#type).expect("invalid axiom");
        }
        Self(parse)
    }
    pub fn add(&mut self, s: &str) -> Result<(), String> {
        self.0.parse(s)
    }
}

const PRELUDE: &str = "
    def HEq: ∀ u: Level, ∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0 :=
        λ u: Level, λ α: Sort u, λ a: α, Ind(Self: ∀ β: Sort u, ∀ b: β, Sort Level:0, Self α a),
    with {
        def HEq:def: ∀ u: Level,
            Ind(Self: (∀ b: (∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0), Sort Level:0),
                Self (λ α: Sort u, λ a: α, Ind(Self: ∀ β: Sort u, ∀ b: β, Sort Level:0, Self α a)))
            (HEq u) :=
            λ u: Level, Ind:constr(
                Self: (∀ b: (∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0), Sort Level:0),
                Self (HEq u));
    }
    def HEq:refl: ∀ u: Level, ∀ α: Sort u, ∀ a: α, HEq u α a α a := λ u: Level, λ α: Sort u, λ a: α,
        Ind:elim(
            Self: (∀ b: (∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0), Sort Level:0),
            Self (λ α: Sort u, λ a: α, Ind(Self: ∀ β: Sort u, ∀ b: β, Sort Level:0, Self α a)))
        Level:0
        (λ b: (∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0),
            λ h: Ind(
                Self: (∀ b: (∀ α: Sort u, ∀ a: α, ∀ β: Sort u, ∀ b: β, Sort Level:0), Sort Level:0),
                Self (λ α: Sort u, λ a: α, Ind(Self: ∀ β: Sort u, ∀ b: β, Sort Level:0, Self α a)))
                b,
            b α a α a)
        Ind:constr(Self: ∀ β: Sort u, ∀ b: β, Sort Level:0, Self α a)
        (HEq u) (HEq:def u);

    def Equiv: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: Sort v, Sort (Level:max u v) :=
        λ u: Level, λ v: Level, λ α: Sort u, λ β: Sort v,
        Ind(Self: Sort (Level:max u v),
            ∀ to: ∀ a: α, β, ∀ of: ∀ b: β, α,
            ∀ of_to: ∀ a: α, HEq u α (of (to a)) α a,
            ∀ to_of: ∀ b: β, HEq v β (to (of b)) β b,
            Self),
    with {
        def Equiv:eq_ind: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: Sort v,
            HEq (Level:s (Level:max u v))
                (Sort (Level:max u v)) (Equiv u v α β)
                (Sort (Level:max u v)) Ind(Self: Sort (Level:max u v),
                    ∀ to: ∀ a: α, β, ∀ of: ∀ b: β, α,
                    ∀ of_to: ∀ a: α, HEq u α (of (to a)) α a,
                    ∀ to_of: ∀ b: β, HEq v β (to (of b)) β b,
                    Self)
            := λ u: Level, λ v: Level, λ α: Sort u, λ β: Sort v,
                HEq:refl (Level:s (Level:max u v)) (Sort (Level:max u v)) (Equiv u v α β);
    }

    def Trunc: ∀ u: Level, ∀ α: Sort u, Sort u := λ u: Level, λ α: Sort u, α,
    with {
        def Trunc:mk: ∀ u: Level, ∀ α: Sort u, ∀ a: α, Trunc u α :=
            λ u: Level, λ α: Sort u, λ a: α, a, with {
        def Trunc:lift: ∀ u: Level, ∀ v: Level, ∀ α: Sort u,
            ∀ motive: (∀ t: Trunc u α, Sort v),
            ∀ f: (∀ a: α, motive (Trunc:mk u α a)),
            ∀ hf: (∀ a: α, ∀ b: α,
                HEq v (motive (Trunc:mk u α a)) (f a) (motive (Trunc:mk u α b)) (f b)),
            ∀ t: Trunc u α,
            motive t := λ u: Level, λ v: Level, λ α: Sort u,
            λ motive: (∀ t: Trunc u α, Sort v),
            λ f: (∀ a: α, motive (Trunc:mk u α a)),
            λ hf: (∀ a: α, ∀ b: α,
                HEq v (motive (Trunc:mk u α a)) (f a) (motive (Trunc:mk u α b)) (f b)),
            λ t: Trunc u α,
            f t;
    }}
";

const AXIOMS: [(&str, &str); 3] = [
    (
        "Prop:ext",
        "∀ a: Sort Level:0, ∀ b: Sort Level:0,
        ∀ h: Equiv Level:0 Level:0 a b, HEq (Level:s Level:0) (Sort Level:0) a (Sort Level:0) b",
    ),
    (
        "Fn:ext",
        "∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort v),
        ∀ f: (∀ x: α, β x), ∀ g: (∀ x: α, β x), ∀ h: (∀ x: α, HEq v (β x) (f x) (β x) (g x)),
        HEq (Level:imax u v) (∀ x: α, β x) f (∀ x: α, β x) g",
    ),
    (
        "Trunc:eq",
        "∀ u: Level, ∀ α: Sort u, ∀ a: Trunc u α, ∀ b: Trunc u α, \
            HEq u (Trunc u α) a (Trunc u α) b",
    ),
];

mod stack;

mod expr;

mod kernel;

mod parse;

#[cfg(test)]
mod tests;
