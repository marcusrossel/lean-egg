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
        let fun_bvars = &graph[subst[self.fun]].data.loose_bvars;
        if fun_bvars.contains(&0) { return vec![] }
        
        let new_fun: PatternAst<LeanExpr> = if fun_bvars.is_empty() {
            format!("{}", self.fun).parse().unwrap()
        } else {
            format!("(↑ - 1 0 {})", self.fun).parse().unwrap()
        };
        
        let (id, _) = graph.union_instantiations(ast.unwrap(), &new_fun, subst, rule);
        vec![id]
    }
}