#[test]
fn init() {
    env_logger::init();
    crate::eval::new_state();
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
        &["Level:max u (Level:s u)", "Level:s u"],
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
            "def test := λ u: Level, λ v: Level, λ w: Level, \
                (λ x: Sort (Level:s ({l})), x) (Sort ({r})) \
                with _"
        );
        let mut state = crate::eval::new_state();
        crate::parse::parse(&mut state, &s)
    }
}
