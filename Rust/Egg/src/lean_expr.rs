use egg::*;

define_language! {
    pub enum LeanExpr {
        // Primitives:
        Nat(u64),
        Str(String),

        // Encoding of universe levels:
        // Note, we don't encode `zero` explicitly and use `Nat(0)` for that instead.
        "uvar"  = UVar(Id),         // (Nat)
        "param" = Param(Id),        // (Str)
        "succ"  = Succ(Id),         // (<level>)
        "max"   = Max([Id; 2]),     // (<level>, <level>)
        "imax"  = IMax([Id; 2]),    // (<level>, <level>)
        
        // Encoding of expressions:
        "bvar"  = BVar(Id),         // (Nat)
        "fvar"  = FVar(Id),         // (Nat)
        "mvar"  = MVar(Id),         // (Nat)
        "sort"  = Sort(Id),         // (<level>)
        "const" = Const(Box<[Id]>), // (Str, <level>*)
        "app"   = App([Id; 2]),     // (<expr>, <expr>)
        "λ"     = Lam([Id; 2]),     // (<expr>, <expr>)
        "∀"     = Forall([Id; 2]),  // (<expr>, <expr>)
        "lit"   = Lit(Id),          // (Nat | Str)

        // Constructs for erasure:
        "proof" = Proof(Id),        // (<expr>)
        "inst"  = Inst(Id),         // (<expr>)

        // Constructs for small-step substitution:
        "↦" = Subst([Id; 3]),       // (Nat, <expr>, <expr>)
        "↑" = Shift([Id; 4]),       // (Str, Nat, Nat, <expr>)

        // Constructs for shape annotations:
        // Note, we don't encode the shape of non-function types explicitly and use `Str("*")`) for that instead.
        "→" = Fun([Id; 2]),         // (<shape>, <shape>)
        "◇" = Shaped([Id; 2]),      // (<shape>, <expr>)

        // Construct for unknown terms (this is used in η-expansion):
        "_" = Unknown,        
    }
} 

impl LeanExpr {

    pub fn is_binder(&self) -> bool {
        match self {
            LeanExpr::Lam(_) | LeanExpr::Forall(_) => true,
            _                                      => false
        }
    }
}