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

        // Constants for erased expressions:
        "_" = Erased,
    }
}

// An expression is considered non-recursive if it can never be part of a loop in an e-graph.
// Note that this is a result of the semantics of each constructor, not of its syntactic form.
pub fn is_nonrec(expr: &LeanExpr) -> bool {
    match expr {
        LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) => false,
        _ => true
    }
}

// An expression `lhs` is smaller than another `rhs` wrt. non-recursiveness if `lhs` not recursive 
// but `rhs` is.
pub fn nonrec_cmp(lhs: &LeanExpr, rhs: &LeanExpr) -> Ordering {
    match (is_nonrec(lhs), is_nonrec(rhs)) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        _             => Ordering::Equal,
    }
}

pub fn swap_child(single_child_node: &LeanExpr, new_child: Id) -> LeanExpr {
    match single_child_node {
        LeanExpr::Lit(_)   => LeanExpr::Lit(new_child),
        LeanExpr::FVar(_)  => LeanExpr::FVar(new_child),
        LeanExpr::MVar(_)  => LeanExpr::MVar(new_child),
        LeanExpr::Sort(_)  => LeanExpr::Sort(new_child),
        LeanExpr::UVar(_)  => LeanExpr::UVar(new_child),
        LeanExpr::Param(_) => LeanExpr::Param(new_child),
        LeanExpr::Succ(_)  => LeanExpr::Succ(new_child),
        _                  => panic!("Called 'swap_child' on 'LeanExpr' containing not exactly one child.")
    }
}

pub fn swap_children(two_child_node: &LeanExpr, new_children: [Id; 2]) -> LeanExpr {
    match two_child_node {
        LeanExpr::Max(_)    => LeanExpr::Max(new_children),
        LeanExpr::IMax(_)   => LeanExpr::IMax(new_children),
        LeanExpr::App(_)    => LeanExpr::App(new_children),
        LeanExpr::Lam(_)    => LeanExpr::Lam(new_children),
        LeanExpr::Forall(_) => LeanExpr::Forall(new_children),
        _                   => panic!("Called 'swap_children' on 'LeanExpr' containing not exactly two children.")
    }
}