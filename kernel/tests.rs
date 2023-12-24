#[test]
fn kernel_new() {
    crate::Kernel::new();
}

#[test]
fn pass() {
    for s in CHECKS {
        log::info!("typechecking\n{s}");
        if let Err(e) = typecheck(s) {
            panic!("error typechecking\n{s}\n{e}");
        }
    }

    const CHECKS: &[&str] = &[
        // False
        "(λ x: Sort Level:0, x) Ind(False: Sort Level:0)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind(False: Sort Level:0), Sort u,
            ∀ t: Ind(False: Sort Level:0),
            motive t,
        x) Ind:elim(False: Sort Level:0)",
        // Empty (universe-polymorphic)
        "λ u: Level, (λ x: Sort u, x) Ind(Empty: Sort u)",
        "λ u: Level, (λ x: ∀ v: Level,
            ∀ motive: ∀ a: Ind(Empty: Sort u), Sort v,
            ∀ t: Ind(Empty: Sort u),
            motive t,
        x) Ind:elim(Empty: Sort u)",
        // True
        "(λ x: Sort Level:0, x) Ind(True: Sort Level:0, True)",
        "(λ x: Ind(True: Sort Level:0, True), x) Ind:constr(True: Sort Level:0, True)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind(True: Sort Level:0, True), Sort u,
            ∀ intro: motive Ind:constr(True: Sort Level:0, True),
            ∀ t: Ind(True: Sort Level:0, True),
            motive t,
        x) Ind:elim(True: Sort Level:0, True)",
        "(λ x: Sort (Level:s Level:0), x)
        (Sort (Ind:elim(True: Sort Level:0, True)
            (Level:s Level:0)
            (λ _: Ind(True: Sort Level:0, True), Level)
            Level:0
            (Ind:constr(True: Sort Level:0, True))))",
        // Unit (universe-polymorphic)
        "λ u: Level, (λ x: Sort u, x) Ind(Unit: Sort u, Unit)",
        "λ u: Level, (λ x: Ind(Unit: Sort u, Unit), x) Ind:constr(Unit: Sort u, Unit)",
        "λ u: Level, (λ x: ∀ v: Level,
            ∀ motive: ∀ a: Ind(Unit: Sort u, Unit), Sort v,
            ∀ intro: motive Ind:constr(Unit: Sort u, Unit),
            ∀ t: Ind(Unit: Sort u, Unit),
            motive t,
        x) Ind:elim(Unit: Sort u, Unit)",
        "λ u: Level, (λ x: Sort (Level:s Level:0), x)
        (Sort (Ind:elim(Unit: Sort u, Unit)
            (Level:s Level:0)
            (λ _: Ind(Unit: Sort u, Unit), Level)
            Level:0
            (Ind:constr(Unit: Sort u, Unit))))",
        // Bool
        "(λ x: Sort (Level:s Level:0), x) Ind(Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: Ind(Bool: Sort (Level:s Level:0), Bool, Bool), x)
            Ind:constr₀(Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: Ind(Bool: Sort (Level:s Level:0), Bool, Bool), x)
            Ind:constr₁(Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind(Bool: Sort (Level:s Level:0), Bool, Bool), Sort u,
            ∀ false: motive Ind:constr₀(Bool: Sort (Level:s Level:0), Bool, Bool),
            ∀  true: motive Ind:constr₁(Bool: Sort (Level:s Level:0), Bool, Bool),
            ∀ b: Ind(Bool: Sort (Level:s Level:0), Bool, Bool),
            motive b,
        x) Ind:elim(Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: Sort (Level:s Level:0), x) (Sort (Ind:elim(Bool: Sort (Level:s Level:0), Bool, Bool)
            (Level:s Level:0) (λ _: Ind(Bool: Sort (Level:s Level:0), Bool, Bool), Level)
            (Level:0) (Level:s Level:0)
            Ind:constr₀(Bool: Sort (Level:s Level:0), Bool, Bool)))",
        "(λ x: Sort (Level:s Level:0), x) (Sort (Ind:elim(Bool: Sort (Level:s Level:0), Bool, Bool)
            (Level:s Level:0) (λ _: Ind(Bool: Sort (Level:s Level:0), Bool, Bool), Level)
            (Level:s Level:0) (Level:0)
            Ind:constr₁(Bool: Sort (Level:s Level:0), Bool, Bool)))",
        // Simple indexed type living in `Prop`
        "(λ x: ∀ α: Sort (Level:s Level:0), Sort Level:0, x)
            Ind(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        "(λ x: Ind(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) (Sort Level:0), x)
            Ind:constr(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ α: Sort (Level:s Level:0),
                ∀ a: Ind(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) α,
                Sort u,
            ∀ intro: motive (Sort Level:0)
                Ind:constr(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)),
            ∀ α: Sort (Level:s Level:0),
            ∀ t: Ind(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) α,
            motive α t,
        x) Ind:elim(T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        // Eq (=)
        "λ u: Level, λ α: Sort u, (λ x: ∀ a: α, ∀ b: α, Sort Level:0, x)
            Ind(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        "λ u: Level, λ α: Sort u,
        (λ x: ∀ a: α, Ind(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a a, x)
            Ind:constr(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        "λ u: Level, λ α: Sort u,
        (λ x: ∀ v: Level,
            ∀ motive:
                ∀ a: α, ∀ b: α,
                ∀ t: Ind(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a b, 
                Sort v,
            ∀ refl: ∀ a: α,
                motive a a (Ind:constr(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a),
            ∀ a: α, ∀ b: α, ∀ t: Ind(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a b,
            motive a b t,
        x) Ind:elim(Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        // Equiv (↔); must support large elimination
        "λ Eq: ∀ u: Level, ∀ α: Sort u, ∀ a: α, ∀ b: α, Sort Level:0,
        λ u: Level, λ v: Level, λ α: Sort u, λ β: Sort v,
        (λ x: Sort (Level:max u v), x)
            Ind(Equiv: Sort (Level:max u v), ∀ to: ∀ a: α, β, ∀ of: ∀ b: β, α,
                ∀ of_to: ∀ a: α, Eq u α (of (to a)) a,
                ∀ to_of: ∀ b: β, Eq v β (to (of b)) b, Equiv)",
        // Recursive application of recursor
        "(
        λ ℕ: Sort (Level:s Level:0), λ 0: ℕ, λ s: (∀ n: ℕ, ℕ),
        λ rec: (∀ u: Level, ∀ motive: (∀ n: ℕ, Sort u),
            ∀ c₀: motive 0,
            ∀ cₛ: (∀ n: ℕ, ∀ ih: motive n, motive (s n)),
            ∀ t: ℕ, motive t),
        λ _: Sort (Level:s
            (rec (Level:s Level:0) (λ _: ℕ, Level) Level:0 (λ _: ℕ, Level:s) (s (s (s (s (s 0))))))),
        ℕ)
        Ind(ℕ: Sort (Level:s Level:0), ℕ, ∀ n: ℕ, ℕ)
        Ind:constr₀(ℕ: Sort (Level:s Level:0), ℕ, ∀ n: ℕ, ℕ)
        Ind:constr₁(ℕ: Sort (Level:s Level:0), ℕ, ∀ n: ℕ, ℕ)
        Ind:elim(ℕ: Sort (Level:s Level:0), ℕ, ∀ n: ℕ, ℕ)
        (Sort (Level:s (Level:s (Level:s (Level:s (Level:s Level:0))))))",
        // A very complex artificial inductive type.
        "λ Bool: Sort (Level:s Level:0), λ false: Bool, λ true: Bool,
        λ ℕ: Sort (Level:s Level:0), λ 0: ℕ, λ 1: ℕ, λ 2: ℕ, λ Unit: Sort (Level:s Level:0),
        λ bool_to_level: (∀ _: Bool, Level), λ sorry: (∀ u: Level, ∀ α: Sort u, α),
        (λ T: (∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0)),
        λ T:c₀: (∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
            T false 0),
        λ T:c₁: T false 2,
        λ T:rec: (∀ u: Level,
            ∀ motive: (∀ x: Bool, ∀ y: ℕ, ∀ t: T x y, Sort u),
            ∀ c₀: (
                ∀ a: (∀ p: Bool, T p 0),
                ∀ b: T true 1,
                ∀ c: Bool,
                ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                ∀ a_rec: (∀ p: Bool, motive p 0 (a p)),
                ∀ b_rec: motive true 1 b,
                ∀ d_rec: (∀ p: ℕ, ∀ q: Unit, motive c 1 (d p q)),
                motive false 0 (T:c₀ a b c d)),
            ∀ c₁: motive false 2 T:c₁,
            ∀ x: Bool, ∀ y: ℕ, ∀ t: T x y, motive x y t),
        λ x: Sort (Level:s (
            T:rec (Level:s Level:0) (λ x: Bool, λ y: ℕ, λ t: T x y, Level)
                (λ a: (∀ p: Bool, T p 0),
                    λ b: T true 1,
                    λ c: Bool,
                    λ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                    λ a_rec: (∀ p: Bool, Level),
                    λ b_rec: Level,
                    λ d_rec: (∀ p: ℕ, ∀ q: Unit, Level),
                    bool_to_level c)
                (Level:s Level:0)
                false 0 (T:c₀
                    (λ p: Bool, sorry (Level:s Level:0) (T p 0))
                    (sorry (Level:s Level:0) (T true 1))
                    false
                    (λ p: ℕ, λ q: Unit, sorry (Level:s Level:0) (T false 1))))),
        λ x: Sort (Level:s (
            T:rec (Level:s Level:0) (λ x: Bool, λ y: ℕ, λ t: T x y, Level)
                (λ a: (∀ p: Bool, T p 0),
                    λ b: T true 1,
                    λ c: Bool,
                    λ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                    λ a_rec: (∀ p: Bool, Level),
                    λ b_rec: Level,
                    λ d_rec: (∀ p: ℕ, ∀ q: Unit, Level),
                    Level:s Level:0)
                (Level:0)
                false 2 T:c₁)),
        0)
        Ind(T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:constr₀(T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:constr₁(T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:elim(T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        (Sort (bool_to_level false))
        Level",
        // Small elimination
        "λ u: Level, λ α: Sort u, (
        λ Nonempty: Sort Level:0,
        λ intro: (∀ a: α, Nonempty),
        λ elim: (
            ∀ motive: (∀ h: Nonempty, Sort Level:0),
            ∀ h: (∀ a: α, motive (intro a)),
            ∀ t: Nonempty, motive t), u)
        Ind(small, Nonempty: Sort Level:0, ∀ a: α, Nonempty)
        Ind:constr₀(small, Nonempty: Sort Level:0, ∀ a: α, Nonempty)
        Ind:elim(small, Nonempty: Sort Level:0, ∀ a: α, Nonempty)",
        "λ P: Sort Level:0, λ Q: Sort Level:0, (
        λ Or: Sort Level:0,
        λ a: (∀ h: P, Or), λ b: (∀ h: Q, Or),
        λ elim: (
            ∀ motive: (∀ h: Or, Sort Level:0),
            ∀ ha: (∀ h: P, motive (a h)),
            ∀ hb: (∀ h: Q, motive (b h)),
            ∀ t: Or, motive t), P)
        Ind(small, Or: Sort Level:0, ∀ h: P, Or, ∀ h: Q, Or)
        Ind:constr₀(small, Or: Sort Level:0, ∀ h: P, Or, ∀ h: Q, Or)
        Ind:constr₁(small, Or: Sort Level:0, ∀ h: P, Or, ∀ h: Q, Or)
        Ind:elim(small, Or: Sort Level:0, ∀ h: P, Or, ∀ h: Q, Or)",
    ];
}

#[test]
fn levels() {
    checks(&[
        &["Level:0", "Level:imax u Level:0"],
        &[
            "u",
            "Level:imax u u",
            "Level:imax Level:0 u",
            "Level:max Level:0 u",
            "Level:max u Level:0",
            "Level:max u u",
            "Level:imax (Level:s Level:0) u",
        ],
        &["v"],
        &["Level:imax u (Level:s v)", "Level:max u (Level:s v)"],
        &[
            "Level:imax u (Level:max v w)",
            "Level:max (Level:imax u v) (Level:imax u w)",
        ],
        &[
            "Level:imax u (Level:imax v w)",
            "Level:max (Level:imax u w) (Level:imax v w)",
            "Level:imax (Level:max u v) w",
        ],
        &[
            "Level:imax u (Level:max (Level:s Level:0) v)",
            "Level:max (Level:s Level:0) (Level:max u v)",
        ],
        &["Level:max (Level:max u v) w", "Level:max u (Level:max v w)"],
        &[
            "Level:max u v",
            "Level:max v u",
            "Level:max (Level:imax u v) (Level:imax v u)",
            "Level:max (Level:imax u v) u",
            "Level:imax u (Level:max u v)",
            "Level:imax (Level:max (Level:s Level:0) (Level:max u v)) (Level:max u v)",
        ],
        &["Level:max (Level:imax u v) v", "Level:imax u v"],
        &[
            "Level:s (Level:s (Level:max u v))",
            "Level:s (Level:max (Level:s v) (Level:s u))",
            "Level:max (Level:s (Level:s v)) (Level:s (Level:s u))",
        ],
        &[
            "Level:max u (Level:s u)",
            "Level:s u",
            "Level:imax (Level:s u) (Level:imax u (Level:s Level:0))",
        ],
    ]);

    checks(&[&[
        "(λ x: Level, (λ x: Level, x) x) u",
        "(λ x: Level, x) u",
        "u",
    ]]);

    fn checks(input: &[&[&str]]) {
        let iter = input
            .iter()
            .enumerate()
            .flat_map(|(i, slice)| slice.iter().map(move |s| (i, s)));
        for (i, a) in iter.clone() {
            for (j, b) in iter.clone() {
                log::debug!("ensuring def_eq({a}, {b}) = {}", i == j);
                match def_eq(a, b) {
                    Err(e) if i == j => panic!("!def_eq({a}, {b}): {e}"),
                    Ok(()) if i != j => panic!("def_eq({a}, {b})"),
                    _ => {}
                }
            }
        }
    }

    fn def_eq(l: &str, r: &str) -> Result<(), String> {
        let s = format!(
            "λ u: Level, λ v: Level, λ w: Level, \
                (λ x: Sort (Level:s ({l})), x) (Sort ({r}))"
        );
        typecheck(&s)
    }
}

fn typecheck(s: &str) -> Result<(), String> {
    crate::parse::State::new().check_expr(s).map(drop)
}
