pub(crate) struct State {
    kernel: kernel::State,
    defs: Vec<Option<fn()>>,
    jit: JitModule,
    functions: cranelift_frontend::FunctionBuilderContext,
}

impl State {
    pub fn new() -> Self {
        let kernel = kernel::State::new();
        let jit = JitBuilder::new(cranelift_module::default_libcall_names()).unwrap();
        Self {
            defs: vec![None; kernel.defs() as usize],
            kernel: kernel::State::new(),
            jit: JitModule::new(jit),
            functions: cranelift_frontend::FunctionBuilderContext::new(),
        }
    }
    pub fn eval(&mut self, e: &Expr) -> Result<(), String> {
        todo!()
    }
}

// optimizations:
// - parameter removal
// - parameter coalescing

fn compile(s: &mut State, e: &Expr) -> Result<*mut u8, String> {
    let mut f = cranelift_codegen::ir::Function::new();
    let mut f = cranelift_frontend::FunctionBuilder::new(&mut f, &mut s.functions);
    let pointer = s.jit.isa().pointer_type();

    todo!()
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
use crate::kernel;
use crate::kernel::consts::*;
use crate::parse;
use cranelift_jit::JITBuilder as JitBuilder;
use cranelift_jit::JITModule as JitModule;
use cranelift_module::Module as _;
