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
        for axiom in AXIOMS.lines() {
            parse.axiom(axiom).unwrap();
        }
        Self(parse)
    }
    pub fn add(&mut self, s: &str) -> Result<(), String> {
        self.0.parse(s)
    }
}

const AXIOMS: &str = "\
Eq: ∀ u: Level, ∀ α: Sort u, ∀ a: α, ∀ b: α, Sort Level:0
Eq:refl: ∀ u: Level, ∀ α: Sort u, ∀ a: α, Eq u α a a
funext: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort v),\
    ∀ f: (∀ a: α, β a), ∀ g: (∀ a: α, β a), ∀ h: (∀ a: α, Eq v (β a) (f a) (g a)),\
    Eq (Level:imax u v) (∀ a: α, β a) f g
propext: ∀ A: Sort Level:0, ∀ B: Sort Level:0, ∀ h₁: (∀ h: A, B), ∀ h₂: (∀ h: B, A),\
    Eq (Level:s Level:0) (Sort Level:0) A B
Eq:elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ motive: (∀ a: α, Sort v), ∀ a: α, ∀ h: motive a,\
    ∀ b: α, ∀ t: Eq u α a b, motive b
Eq:refl_elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ motive: (∀ a: α, Sort v), ∀ a: α,\
    ∀ h: motive a, Eq v (motive a) (Eq:elim u v α motive a h a (Eq:refl u α a)) h
Sigma: ∀ u: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u), Sort u
Sigma:mk: ∀ u: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u), ∀ a: α, ∀ b: β a, Sigma u α β
Sigma:elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u),\
    ∀ motive: (∀ t: Sigma u α β, Sort v), ∀ h: (∀ a: α, ∀ b: β a, motive (Sigma:mk u α β a b)),\
    ∀ t: Sigma u α β, motive t
Sigma:mk_elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u),\
    ∀ motive: (∀ t: Sigma u α β, Sort v), ∀ h: (∀ a: α, ∀ b: β a, motive (Sigma:mk u α β a b)),\
    ∀ a: α, ∀ b: β a,\
    Eq v (motive (Sigma:mk u α β a b)) (Sigma:elim u v α β motive h (Sigma:mk u α β a b)) (h a b)
Bool: Sort (Level:s Level:0)
false: Bool
true: Bool
Bool:elim: ∀ u: Level, ∀ motive: (∀ t: Bool, Sort u), ∀ h₁: motive false, ∀ h₂: motive true,\
    ∀ t: Bool, motive t
false_elim: ∀ u: Level, ∀ motive: (∀ t: Bool, Sort u), ∀ h₁: motive false, ∀ h₂: motive true,\
    Eq u (motive false) (Bool:elim u motive h₁ h₂ false) h₁
true_elim: ∀ u: Level, ∀ motive: (∀ t: Bool, Sort u), ∀ h₁: motive false, ∀ h₂: motive true,\
    Eq u (motive true) (Bool:elim u motive h₁ h₂ true) h₂
ULift: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, Sort (Level:max u v)
ULift:up: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ a: α, ULift u v α
ULift:down: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ a: ULift u v α, α
ULift:up_down: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ a: α,\
    Eq u α (ULift:down u v α (ULift:up u v α a)) a
ULift:down_up: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ a: ULift u v α,\
    Eq (Level:max u v) (ULift u v α) (ULift:up u v α (ULift:down u v α a)) a
W: ∀ u: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u), Sort u
W:mk: ∀ u: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u), ∀ a: α, ∀ b: (∀ i: β a, W u α β), W u α β
W:elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u),\
    ∀ motive: (∀ t: W u α β, Sort v),\
    ∀ f: (∀ a: α, ∀ b: (∀ i: β a, W u α β), ∀ r: (∀ i: β a, motive (b i)),\
        motive (W:mk u α β a b)),\
    ∀ t: W u α β, motive t
W:mk_elim: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ β: (∀ a: α, Sort u),\
    ∀ motive: (∀ t: W u α β, Sort v),\
    ∀ f: (∀ a: α, ∀ b: (∀ i: β a, W u α β), ∀ r: (∀ i: β a, motive (b i)),\
        motive (W:mk u α β a b)),\
    ∀ a: α, ∀ b: (∀ i: β a, W u α β), Eq v (motive (W:mk u α β a b))\
        (W:elim u v α β motive f (W:mk u α β a b))\
        (f a b (λ i: β a, W:elim u v α β motive f (b i)))
Inhabited: ∀ u: Level, ∀ α: Sort u, Sort Level:0
Inhabited:mk: ∀ u: Level, ∀ α: Sort u, ∀ a: α, Inhabited u α
Inhabited:elim_subsingleton: ∀ u: Level, ∀ v: Level, ∀ α: Sort u, ∀ motive: Sort v,\
    ∀ h: (∀ a b: motive, Eq v motive a b), ∀ f: (∀ a: α, motive),\
    ∀ t: Inhabited u α, motive
";

mod stack;

mod expr;

mod kernel;

mod parse;

#[cfg(test)]
mod tests;
