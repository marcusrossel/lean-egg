use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::shift::*;

struct Eta {
    fun: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Eta {

    fn apply_one(&self, egraph: &mut LeanEGraph, eta_class: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let fun_class = subst[self.fun];
        if egraph[fun_class].data.bvars.contains(&0) { return vec![] }
        let shifted_fun_class = shift_loose_bvars(-1, fun_class, egraph, rule);
        if egraph.union_trusted(eta_class, shifted_fun_class, rule) {
            vec![eta_class]
        } else {
            vec![]
        }
    }
}

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("≡η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : "?f".parse().unwrap() }})
}
