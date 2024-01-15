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

fn check_eq(init: String, goal: String, rws: &[CRewrite], optimize_expl: bool) -> Option<String> {
    let mut egraph: EGraph<LeanExpr, ()> = Default::default();
    egraph = egraph.with_explanations_enabled();
    if !optimize_expl { egraph = egraph.without_explanation_length_optimization() }
    let init_expr = init.parse().unwrap();
    let goal_expr = goal.parse().unwrap();
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);
    let rules = rules_for_c_rewrites(rws);
    let mut runner = Runner::default()
        .with_egraph(egraph)
        .with_hook(move |runner| {
            if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
                Err("search complete".to_string())
            } else {
                Ok(())
            }
       })
        .run(&rules);
    if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
        Some(runner.explain_equivalence(&init_expr, &goal_expr).get_string())
    } else {
        None
    }
}

#[no_mangle]
pub extern "C" fn c_egg_check_eq(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws_ptr: *const CRewrite, 
    rws_count: usize,
    optimize_expl: bool
) -> EggResult {
    // Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
    let init_c_str = unsafe { CStr::from_ptr(init_str_ptr) };
    let goal_c_str = unsafe { CStr::from_ptr(goal_str_ptr) };
    let init = String::from_utf8_lossy(init_c_str.to_bytes()).to_string();
    let goal = String::from_utf8_lossy(goal_c_str.to_bytes()).to_string();
    assert!(rws_ptr != null()); 
    let rws = unsafe { std::slice::from_raw_parts(rws_ptr, rws_count) };
    if let Some(expl) = check_eq(init, goal, rws, optimize_expl) {
        let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");
        // Note: The `into_raw` here is important, as otherwise Rust deallocates the string.
        // TODO: I think this is a memory leak right now.
        EggResult { success: true,  expl: expl_c_str.into_raw() }
    } else {
        EggResult { success: false, expl: null() }
    }
}