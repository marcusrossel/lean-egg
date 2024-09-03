use std::collections::HashSet;
use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("≡η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : "?f".parse().unwrap() }})
}

struct Eta {
    fun: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Eta {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let fun_class = subst[self.fun];
        if graph[fun_class].data.loose_bvars.contains(&0) { return vec![] }

        let shifted_fun = down_shift_loose_bvars(&self.fun, &graph[fun_class].data.loose_bvars);
        let (id, _) = graph.union_instantiations(ast.unwrap(), &shifted_fun, subst, rule);
        vec![id]
    }
}

// As substitution does not occurr "all at once", it is important that we apply the 
// substitutions ordered from smaller to larger indices (as the offset is negative).
// Otherwise, indices might be  shifted multiple times as in `(↦ 1 0 (↦ 2 1 e))`, 
// which ends up shifting 2 to 0, whereas `(↦ 2 1 (↦ 1 0 e))` does not.
fn down_shift_loose_bvars(target: &Var, bvars: &HashSet<u64>) -> PatternAst<LeanExpr> {
    let mut shifted = format!("{}", target).parse().unwrap();
    let mut sorted_bvars = bvars.iter().collect::<Vec<_>>();
    sorted_bvars.sort();
    for var in sorted_bvars {
        shifted = format!("(↦ {} {} {})", var, *var - 1, shifted).parse().unwrap();
    }
    shifted
}