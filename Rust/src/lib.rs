use egg::*;
use core::ffi::c_char;
use core::ffi::CStr;
use std::ffi::CString;
use std::ptr::null;
use std::str::FromStr;

// TODO: Remove
extern "C" {
    fn trace(str: *const c_char);
}

#[repr(C)]
#[derive(PartialEq)]
pub enum RewriteDirection {
    Forward,
    Backward,
    Both
}

#[repr(C)]
pub struct CRewrite {
    name: *const c_char,
    lhs:  *const c_char,
    rhs:  *const c_char,
    dir:  RewriteDirection
}

#[repr(C)]
pub struct EggResult {
    success: bool,
    expl:    *const c_char,
}

// TODO:
//
// We don't encode the `bvar`, `fvar`, `mvar`, `letE`, `mdata` and `proj` constructors.
// That is, if we want to convert a `Lean.Expr` to `LeanExpr`, we need to:
// * prune occurrences of `letE`
// * prune occurrences of `mdata`
// * replace occurrences of `proj` with applications of the target type's recursor
//
// Also, since `lam` and `forallE` use bvars, can we throw away the variable name?
//
// Note, we need to be able to handle metavariables, as e.g. if we `apply Eq.trans`
// a goal may have the type `t = ?m`.
// Can we merge FVars and MVars though? They're not distinguishable for the purposes of
// rewriting are they? And can we perhaps even do the same for bvars?
// I think eliminating mvars should be easy as we should probably use `mkLambdaFVars` 
// (cf. Metaprogramming Book) anyway. In fact, then we should also be able to replace
// all bvars by fvars (using forallTelescope), so all we're left with is fvars.
// Note: We might not actually want to do that in Lean, as it might be computationally
// expensive, but what this goes to show is that we can flatten all three types of
// variables to a single kind of variable. In the context of egg, these variables are 
// the metavariables in rewrites ("?asdf"), so we dont even need an explicit representation
// of them in LeanExpr. PROBLEM: You still need a notion of variables for the goal terms
// don't you? E.g. if you're trying to rewrite `?b = 0` to `0 = ?b`, that `?b` is an mvar
// in the goal term which you can't just remove.
//
// Note: In the `lam` and `forallE` constructors, we remove the variable name as the bodies
//       use bvars anyway, as well as the binder-info as it is redundant.
//
//
// PROBLEM: with bvars. E.g. `(fun x : Nat => x) = (fun y : Nat => id y)` becomes `(lam Nat (bvar 0)) = (lam Nat (app id (bvar 0)))`
//          If we represent bvars as egg-metavars, we get: `(lam Nat ?0) = (lam Nat (app id ?0))`.
//          So now we've accidentally merged the two distinct bvars into one mvar.
//          SOLUTION?: Don't turn bvars into egg-vars, as they should actually never be substituted, unless we provide an
//                     explicit rule like beta-reduction which then should then explicitly match on `bvar` though.
//
// Remember, we don't need to be able to reconstruct Lean terms from these LeanExpr terms.
// We only need the sequence of rewrites.

// NOTE:
// An example that doesn't work without either ignoring or properly encoding universe variables is:
//
// -- Solution: rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse]
// example {l₁ l₂ : List α} : l₁ ++ l₂ = (l₂.reverse ++ l₁.reverse).reverse := by
//   egg [List.reverse_append, List.reverse_reverse]

// TODO: If type ascriptions become the norm, you can remove the τ constructor and instead add the types as the first arguments of all other constructors.
//       This would be similar (though not equivalent) to the λ_x approach shown in Kœhler's dissertation.
define_language! {
    enum LeanExpr {
        // Primitives:
        BVarId(i32),
        FVarId(i32),
        MVarId(i32),
        UVarId(i32),
        TypeId(i32),
        Name(String),
        NatLit(i64),   
        StrLit(String),

        // Encoding of universe levels:
        // Note, we don't encode `zero` explicitly, and use `NatLit(0)` for that instead.
        "uvar"  = UVar(Id),         // (UVarId)
        "param" = Param(Id),        // (Name)
        "succ"  = Succ(Id),         // (<level>)
        "max"   = Max([Id; 2]),     // (<level>, <level>)
        "imax"  = IMax([Id; 2]),    // (<level>, <level>)
        
        // Encoding of expressions:
        "bvar"  = BVar(Id),         // (BVarId)
        "fvar"  = FVar(Id),         // (FVarId)
        "mvar"  = MVar(Id),         // (MVarId)
        "sort"  = Sort(Id),         // (<level>)
        "const" = Const(Box<[Id]>), // (Name, <level>*)
        "app"   = App([Id; 2]),     // (<expr>, <expr>)
        "λ"     = Lam(Id),          // (<expr>)
        "∀"     = Forall([Id; 2]),  // (<expr>, <expr>)
        "lit"   = Lit(Id),          // (NatLit | StrLit)

        // Constant for proof erasure:
        "proof" = Proof,

        // Tag for explicit type annotations:
        "τ"     = Typed([Id; 2]), // (TypeId | <expr>, <expr>)
    }
}

fn rules_for_c_rewrites(rws: &[CRewrite]) -> Vec<Rewrite<LeanExpr, ()>> {
    rws.iter().fold(vec![], |mut acc, rw| {
        let name_c_str = unsafe { CStr::from_ptr(rw.name) };
        let lhs_c_str  = unsafe { CStr::from_ptr(rw.lhs) };
        let rhs_c_str  = unsafe { CStr::from_ptr(rw.rhs) };
        let name_str   = name_c_str.to_str().unwrap();
        let lhs_str    = lhs_c_str.to_str().unwrap();
        let rhs_str    = rhs_c_str.to_str().unwrap();
        let lhs        = Pattern::from_str(lhs_str).expect("Failed to parse lhs");
        let rhs        = Pattern::from_str(rhs_str).expect("Failed to parse rhs");
        if rw.dir == RewriteDirection::Forward || rw.dir == RewriteDirection::Both {
            acc.push(Rewrite::new(name_str, lhs.clone(), rhs.clone()).expect("Failed to parse rule"));
        }
        if rw.dir == RewriteDirection::Backward || rw.dir == RewriteDirection::Both {
            // It is important that we use the "-rev" suffix for reverse rules here, as this is also
            // what's used for adding the reverse rule when using egg's `rewrite!(_; _ <=> _)` macro.
            // If we choose another naming scheme, egg may complain about duplicate rules when 
            // `rw.dir == RewriteDirection::Both`. This is the case, for example, for the rewrite
            // `?a + ?b = ?b + ?a`.
            acc.push(Rewrite::new(format!("{name_str}-rev"), rhs, lhs).expect("Failed to parse rule"));
        }
        acc
    })
}

// TODO: Do we need to call egraph.rebuild() anywhere?
fn check_eq(init: String, goal: String, rws: &[CRewrite]) -> Option<String> {
    let mut egraph: EGraph<LeanExpr, ()> = Default::default();
    egraph = egraph.with_explanations_enabled();
    let init_expr = init.parse().unwrap();
    let goal_expr = goal.parse().unwrap();
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);
    let rules = rules_for_c_rewrites(rws);
    let mut runner = Runner::default().with_egraph(egraph).run(&rules);
    if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
        Some(runner.explain_equivalence(&init_expr, &goal_expr).get_string())
    } else {
        None
    }
}

#[no_mangle]
pub extern "C" fn c_egg_check_eq(init_str_ptr: *const c_char, goal_str_ptr: *const c_char, rws_ptr: *const CRewrite, rws_count: usize) -> EggResult {
    // Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
    let init_c_str = unsafe { CStr::from_ptr(init_str_ptr) };
    let goal_c_str = unsafe { CStr::from_ptr(goal_str_ptr) };
    let init = String::from_utf8_lossy(init_c_str.to_bytes()).to_string();
    let goal = String::from_utf8_lossy(goal_c_str.to_bytes()).to_string();
    assert!(rws_ptr != null()); 
    let rws = unsafe { std::slice::from_raw_parts(rws_ptr, rws_count) };
    if let Some(expl) = check_eq(init, goal, rws) {
        let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");
        // Note: The `into_raw` here is important, as otherwise Rust deallocates the string.
        // TODO: I think this is a memory leak right now.
        EggResult { success: true,  expl: expl_c_str.into_raw() }
    } else {
        EggResult { success: false, expl: null() }
    }
}

/*
fn simplify_and_explain(s: &str) -> Explanation<FCPLang> {
    let expr: RecExpr<FCPLang> = s.parse().unwrap();
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr).run(&make_rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best) = extractor.find_best(root);
    runner.explain_equivalence(&expr, &best)
}
*/