#[test]
fn init_eval() {
    crate::eval::State::new();
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
        "(λ x: Sort Level:0, x) Ind (False: Sort Level:0)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind (False: Sort Level:0), Sort u,
            ∀ t: Ind (False: Sort Level:0),
            motive t,
        x) Ind:elim (False: Sort Level:0)",
        // Empty (universe-polymorphic)
        "λ u: Level, (λ x: Sort u, x) Ind (Empty: Sort u)",
        "λ u: Level, (λ x: ∀ v: Level,
            ∀ motive: ∀ a: Ind (Empty: Sort u), Sort v,
            ∀ t: Ind (Empty: Sort u),
            motive t,
        x) Ind:elim (Empty: Sort u)",
        // True
        "(λ x: Sort Level:0, x) Ind (True: Sort Level:0, True)",
        "(λ x: Ind (True: Sort Level:0, True), x) Ind:constr 0 (True: Sort Level:0, True)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind (True: Sort Level:0, True), Sort u,
            ∀ intro: motive Ind:constr 0 (True: Sort Level:0, True),
            ∀ t: Ind (True: Sort Level:0, True),
            motive t,
        x) Ind:elim (True: Sort Level:0, True)",
        // Unit (universe-polymorphic)
        "λ u: Level, (λ x: Sort u, x) Ind (Unit: Sort u, Unit)",
        "λ u: Level, (λ x: Ind (Unit: Sort u, Unit), x) Ind:constr 0 (Unit: Sort u, Unit)",
        "λ u: Level, (λ x: ∀ v: Level,
            ∀ motive: ∀ a: Ind (Unit: Sort u, Unit), Sort v,
            ∀ intro: motive Ind:constr 0 (Unit: Sort u, Unit),
            ∀ t: Ind (Unit: Sort u, Unit),
            motive t,
        x) Ind:elim (Unit: Sort u, Unit)",
        // Bool
        "(λ x: Sort (Level:s Level:0), x) Ind (Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: Ind (Bool: Sort (Level:s Level:0), Bool, Bool), x)
            Ind:constr 0 (Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: Ind (Bool: Sort (Level:s Level:0), Bool, Bool), x)
            Ind:constr 1 (Bool: Sort (Level:s Level:0), Bool, Bool)",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ a: Ind (Bool: Sort (Level:s Level:0), Bool, Bool), Sort u,
            ∀ false: motive Ind:constr 0 (Bool: Sort (Level:s Level:0), Bool, Bool),
            ∀  true: motive Ind:constr 1 (Bool: Sort (Level:s Level:0), Bool, Bool),
            ∀ b: Ind (Bool: Sort (Level:s Level:0), Bool, Bool),
            motive b,
        x) Ind:elim (Bool: Sort (Level:s Level:0), Bool, Bool)",
        // Simple indexed type living in `Prop`
        "(λ x: ∀ α: Sort (Level:s Level:0), Sort Level:0, x)
            Ind (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        "(λ x: Ind (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) (Sort Level:0), x)
            Ind:constr 0 (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        "(λ x: ∀ u: Level,
            ∀ motive: ∀ α: Sort (Level:s Level:0),
                ∀ a: Ind (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) α,
                Sort u,
            ∀ intro: motive (Sort Level:0)
                Ind:constr 0 (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)),
            ∀ α: Sort (Level:s Level:0),
            ∀ t: Ind (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0)) α,
            motive α t,
        x) Ind:elim (T: ∀ α: Sort (Level:s Level:0), Sort Level:0, T (Sort Level:0))",
        // Eq (=)
        "λ u: Level, λ α: Sort u, (λ x: ∀ a: α, ∀ b: α, Sort Level:0, x)
            Ind (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        "λ u: Level, λ α: Sort u,
        (λ x: ∀ a: α, Ind (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a a, x)
            Ind:constr 0 (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        "λ u: Level, λ α: Sort u,
        (λ x: ∀ v: Level,
            ∀ motive:
                ∀ a: α, ∀ b: α,
                ∀ t: Ind (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a b, 
                Sort v,
            ∀ refl: ∀ a: α,
                motive a a (Ind:constr 0 (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a),
            ∀ a: α, ∀ b: α, ∀ t: Ind (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a) a b,
            motive a b t,
        x) Ind:elim (Eq: ∀ a: α, ∀ b: α, Sort Level:0, ∀ a: α, Eq a a)",
        // Equiv (↔); must support large elimination
        "λ Eq: ∀ u: Level, ∀ α: Sort u, ∀ a: α, ∀ b: α, Sort Level:0,
        λ u: Level, λ v: Level, λ α: Sort u, λ β: Sort v,
        (λ x: Sort (Level:max u v), x)
            Ind (Equiv: Sort (Level:max u v), ∀ to: ∀ a: α, β, ∀ of: ∀ b: β, α,
                ∀ of_to: ∀ a: α, Eq u α (of (to a)) a,
                ∀ to_of: ∀ b: β, Eq v β (to (of b)) b, Equiv)",
        // A very complex artificial inductive type.
        "λ Bool: Sort (Level:s Level:0), λ false: Bool, λ true: Bool,
        λ ℕ: Sort (Level:s Level:0), λ 0: ℕ, λ 1: ℕ, λ 2: ℕ, λ Unit: Sort (Level:s Level:0),
        (λ T: (∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0)),
        λ T:c₀: (∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
            T false 0),
        λ T:c₁: T false 2,
        λ x: (∀ u: Level,
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
            ∀ x: Bool, ∀ y: ℕ, ∀ t: T x y, motive x y t), x)
        Ind (T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:constr 0 (T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:constr 1 (T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)
        Ind:elim (T: ∀ x: Bool, ∀ y: ℕ, Sort (Level:s Level:0),
            ∀ a: (∀ p: Bool, T p 0), ∀ b: T true 1, ∀ c: Bool, ∀ d: (∀ p: ℕ, ∀ q: Unit, T c 1),
                T false 0,
            T false 2)",
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
    let mut parse = crate::parse::State::new();
    let e = parse.whole_expr(s)?;
    parse.type_check(&e)?;
    Ok(())
}
