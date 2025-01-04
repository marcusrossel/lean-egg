use egg::*;

define_language! {
    pub enum LeanExpr {
        // Primitives:
        Nat(u64),
        Str(String),

        // Encoding of universe levels:
        // Note, we don't encode `zero` explicitly and use `Nat(0)` for that instead.
        "uvar"  = UVar(Id),      // (Nat)
        "param" = Param(Id),     // (Str)
        "succ"  = Succ(Id),      // (<level>)
        "max"   = Max([Id; 2]),  // (<level>, <level>)
        "imax"  = IMax([Id; 2]), // (<level>, <level>)
        
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
        // Note that we also use these constructors to tag rewrite conditions (depending on whether
        // it's a type class or propositional condition).
        "proof" = Proof(Id), // (<expr>)
        "inst"  = Inst(Id),  // (<expr>)

        // Construct for representing equality:
        // We use this *instead* of Lean's equality symbol `Eq` to solve two problems:
        // (1) When reifying equality, we can't determine the universe level and type arguments of
        //     equality and would have to use the `Unknown` constructor for them. If a condition of
        //     a rewrite is an equality with fixed universe level and type, it therefore won't match 
        //     a reified equality. 
        // (2) If we want to maintain a reified equality e-node per e-class, the equality e-node 
        //     must be flat (ie., not require intermediate e-nodes as in `(app (const "Eq" _) ...)`)
        //     in order to reach a fixed point for reifying equality. If we used Lean's equality for
        //     reification instead, then reifying a term `t` would also yield a new intermediate 
        //     term `(app (app (const "Eq" _) _) t)`. This term would itself require a reified 
        //     equality e-node which would yield the intermediate term 
        //     `(app (app (const "Eq" _) _) (app (app (const "Eq" _) _) t))`, etc.
        //     With a flat equality constructor, the only node we add is `(= t t)` which we add to
        //     the e-class of `True` which already has a reified equality node.
        //
        // Note also, as this explicit equality constructor cannot represent partial applications of 
        // Lean's `Eq`, and full applications of `Eq` may only manifest during eqsat, we add a
        // rewrite of the form `(app (app (app (const "Eq" ?u) ?t) ?l) ?r) => (= ?l ?r)` to turn 
        // such occurrences of `Eq` into the explicit equality constructor again.
        "=" = Eq([Id; 2]), // (<expr>, <expr>)

        // Construct for marking the e-class of facts syntactically. That is, we always expect to
        // have exactly one e-node `fact <i>` with `i` denoting the e-class of `const "True"`.
        "fact" = Fact(Id),

        // Constructs for small-step substitution:
        "↦" = Subst([Id; 3]), // (Nat, <expr>, <expr>)
        "↑" = Shift([Id; 4]), // (Str, Nat, Nat, <expr>)

        // Constructs for shape annotations:
        // Note, we don't encode the shape of non-function types explicitly and use `Str("*")`) for that instead.
        "→" = Fun([Id; 2]),    // (<shape>, <shape>)
        "◇" = Shaped([Id; 2]), // (<shape>, <expr>)

        // Construct for unknown terms (this is used when reifying equality and for η-expansion):
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