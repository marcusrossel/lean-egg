use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("≡η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : "?f".parse().unwrap() }})
}

pub fn eta_expansion_rw() -> LeanRewrite {
    rewrite!("≡η+"; "?e" => { EtaExpand { term : "?e".parse().unwrap() }})
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
        
        let (id, did_union) = graph.union_instantiations(ast.unwrap(), &new_fun, subst, rule);
        if did_union { vec![id] } else { vec![] }
    }
}

struct EtaExpand {
    term: Var
}

impl Applier<LeanExpr, LeanAnalysis> for EtaExpand {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let term_bvars = &graph[subst[self.term]].data.loose_bvars;
        
        let new_term: PatternAst<LeanExpr> = if term_bvars.is_empty() {
            format!("{}", self.term).parse().unwrap()
        } else {
            format!("(↑ + 1 0 {})", self.term).parse().unwrap()
        };

        let expanded = format!("(λ _ (app {} (bvar 0)))", new_term).parse().unwrap();
        
        let (id, did_union) = graph.union_instantiations(ast.unwrap(), &expanded, subst, rule);
        if did_union { vec![id] } else { vec![] }
    }
}