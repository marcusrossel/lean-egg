use egg::*;
use core::ffi::c_char;
use core::ffi::CStr;
use std::ffi::CString;
use std::ptr::null;
use std::str::FromStr;

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
        "λ"     = Lam(Id),          // (<expr>)
        "∀"     = Forall(Id),       // (<expr>)
        "lit"   = Lit(Id),          // (Nat | Str)

        // Constant for proof erasure:
        "proof" = Proof,

        // Tag for explicit type annotations:
        "τ"     = Typed([Id; 2]),   // (TypeId | <expr>, <expr>)
    }
}

#[derive(Default)]
struct NatLitAnalysis;
impl Analysis<LeanExpr> for NatLitAnalysis {
    type Data = Option<u64>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        // This prefers `Some` value over `None`. Note that if `to` and `from` are both present,
        // then they should have the same value as otherwise the merging of their e-classes indicates 
        // an invalid rewrite.
        egg::merge_max(to, from)
    }

    // Note: We also assign all `Nat` nodes a value, but that shouldn't be a problem as different `Nat` 
    //       nodes should never belong to the same e-class.
    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {
        match enode {
            LeanExpr::Nat(n) => Some(*n),
            LeanExpr::Lit(l) => egraph[*l].data,
            _ => None
        }
    }
}

/*
// From https://docs.rs/egg/latest/egg/trait.Condition.html:
// "any function (`Fn`) that doesn’t mutate other state and matches the signature of `check`` implements `Condition`"
fn is_gt_zero(v: Var) -> impl Fn(&mut EGraph<LeanExpr, NatLitAnalysis>, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v]].data.is_some_and(|x| x > 0)
}
*/

// TODO: We might be able to merge `ToSucc` and `OfSucc` using `apply_one`'s `rule_name` argument.

#[derive(Debug, Clone, PartialEq, Eq)]
struct ToSucc {
    lit_val: Var
}

impl Applier<LeanExpr, NatLitAnalysis> for ToSucc {

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, matched_id: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, _: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            if lit_val > 0 {
                let pred = egraph.add(LeanExpr::Nat(lit_val - 1));
                let pred_lit = egraph.add(LeanExpr::Lit(pred));
                let succ_name = egraph.add(LeanExpr::Str("Nat.succ".to_string()));
                let succ_const = egraph.add(LeanExpr::Const(Box::new([succ_name])));
                let app_succ_pred = egraph.add(LeanExpr::App([succ_const, pred_lit]));
                if egraph.union(matched_id, app_succ_pred) {
                    return vec![app_succ_pred]
                } 
            }
        }
        vec![]
    }
}

struct OfSucc {
    lit_val: Var
}

impl Applier<LeanExpr, NatLitAnalysis> for OfSucc {

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, matched_id: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, _: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            let succ = egraph.add(LeanExpr::Nat(lit_val + 1));
            let succ_lit = egraph.add(LeanExpr::Lit(succ));
            if egraph.union(matched_id, succ_lit) {
                return vec![succ_lit]
            } 
        }
        vec![]
    }
}

// TODO: Mention in the thesis that this uses dynamic rewrites, which is also why we can't implement it 
//       as a `Egg.Rewrite` in Lean.
fn nat_lit_rws() -> Vec<Rewrite<LeanExpr, NatLitAnalysis>> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("!z"; "(lit 0)"                         <=> "(const Nat.zero)"));
    rws.push(       rewrite!("!t"; "(lit ?n)"                        => { ToSucc { lit_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("!o"; "(app (const Nat.succ) (lit ?n))" => { OfSucc { lit_val : "?n".parse().unwrap() }}));
    rws
}

fn rules_for_c_rewrites(rws: &[CRewrite], gen_nat_lit_rws: bool) -> Vec<Rewrite<LeanExpr, NatLitAnalysis>> {
    let mut rules = rws.iter().fold(vec![], |mut acc, rw| {
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
    });
    if gen_nat_lit_rws { rules.append(&mut nat_lit_rws()) }
    rules
}

fn explain_congr(init: String, goal: String, rws: &[CRewrite], optimize_expl: bool, gen_nat_lit_rws: bool) -> Option<String> {
    let mut egraph: EGraph<LeanExpr, NatLitAnalysis> = Default::default();
    egraph = egraph.with_explanations_enabled();
    if !optimize_expl { egraph = egraph.without_explanation_length_optimization() }
    let init_expr = init.parse().unwrap();
    let goal_expr = goal.parse().unwrap();
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);
    let rules = rules_for_c_rewrites(rws, gen_nat_lit_rws);
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
        let mut expl = runner.explain_equivalence(&init_expr, &goal_expr);
        let expl_str = expl.get_flat_string();
        Some(expl_str)
    } else {
        None
    }
}

#[no_mangle]
pub extern "C" fn c_egg_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws_ptr: *const CRewrite, 
    rws_count: usize,
    optimize_expl: bool,
    gen_nat_lit_rws: bool
) -> EggResult {
    // Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
    let init_c_str = unsafe { CStr::from_ptr(init_str_ptr) };
    let goal_c_str = unsafe { CStr::from_ptr(goal_str_ptr) };
    let init = String::from_utf8_lossy(init_c_str.to_bytes()).to_string();
    let goal = String::from_utf8_lossy(goal_c_str.to_bytes()).to_string();
    assert!(rws_ptr != null()); 
    let rws = unsafe { std::slice::from_raw_parts(rws_ptr, rws_count) };
    if let Some(expl) = explain_congr(init, goal, rws, optimize_expl, gen_nat_lit_rws) {
        let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");
        // Note: The `into_raw` here is important, as otherwise Rust deallocates the string.
        // TODO: I think this is a memory leak right now.
        EggResult { success: true,  expl: expl_c_str.into_raw() }
    } else {
        EggResult { success: false, expl: null() }
    }
}