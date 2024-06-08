use egg::*;
use std::cmp::Ordering;

// TODO: If type ascriptions become the norm, you can remove the τ constructor and instead add the types as the first arguments of all other constructors.
//       This would be similar (though not equivalent) to the λ_x approach shown in Kœhler's dissertation.
define_language! {
    pub enum LeanExpr {
        // Primitives:
        Nat(u64),
        Str(String),

        // Encoding of universe levels:
        // Note, we don't encode `zero` explicitly, and use `Nat(0)` for that instead.
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

        // Constant for proof erasure:
        "proof" = Proof(Id),
    }
}

impl LeanExpr {

    pub fn bvar_idx(&self) -> Option<&Id> {
        match self {
            LeanExpr::BVar(idx) => Some(idx),
            _                   => None
        }    
    }

    pub fn is_binder(&self) -> bool {
        match self {
            LeanExpr::Lam(_) | LeanExpr::Forall(_) => true,
            _                                      => false
        }
    }

    // An expression is considered recursive if it can be part of a loop in an e-graph.
    // Note that this is a result of the semantics of each constructor, not of its syntactic form.
    pub fn is_rec(&self) -> bool {
        match self {
            LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) => true,
            _                                                                              => false
        }
    }

    // An expression `lhs` is smaller than another `rhs` wrt. recursiveness if `lhs` is not 
    // recursive but `rhs` is. If both are either recursive or non-recursive, the total order
    // derived by `define_language!` applies.
    pub fn rec_cmp(&self, rhs: &LeanExpr) -> Ordering {
        match (&self.is_rec(), rhs.is_rec()) {
            (false, true) => Ordering::Less,
            (true, false) => Ordering::Greater,
            _             => self.cmp(rhs),
        }
    }
}