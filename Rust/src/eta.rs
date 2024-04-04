use std::cmp::Ordering;
use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::subst::*;

struct Eta {
    fun: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Eta {

    fn apply_one(&self, egraph: &mut LeanEGraph, eta_class: Id, s: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let fun_class = s[self.fun];
        if egraph[fun_class].data.loose_bvars.contains(&0) { return vec![] }
        let shifted_fun_class = subst(fun_class, egraph, rule, &shift_down_loose_bvar);
        if egraph.union_trusted(eta_class, shifted_fun_class, rule) {
            vec![eta_class]
        } else {
            vec![]
        }
    }
}

fn shift_down_loose_bvar(idx: u64, binder_depth: u64, egraph: &mut LeanEGraph) -> LeanExpr {
    match idx.cmp(&binder_depth) {
        Ordering::Greater => LeanExpr::BVar(egraph.add(LeanExpr::Nat(idx - 1))),
        Ordering::Equal   => panic!("η-reduction encountered invalid bvar"),
        Ordering::Less    => unreachable!() // `subst` provides the invariant that `idx >= binder_depth`.
    }
}

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("≡η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : "?f".parse().unwrap() }})
}
