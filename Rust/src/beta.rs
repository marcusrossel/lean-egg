use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("≡β"; "(app (λ ?t ?b) ?a)" => { Beta { body : "?b".parse().unwrap(), arg : "?a".parse().unwrap() }})
}

struct Beta {
    body: Var,
    arg:  Var
}

impl Applier<LeanExpr, LeanAnalysis> for Beta {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let arg_bvars = &graph[subst[self.arg]].data.loose_bvars;
        let body_bvars = &graph[subst[self.body]].data.loose_bvars;

        let shifted_arg: PatternAst<LeanExpr> = if arg_bvars.is_empty() {
            format!("{}", self.arg).parse().unwrap()
        } else {
            format!("(↑ + 1 0 {})", self.arg).parse().unwrap()
        };

        let sub: PatternAst<LeanExpr> = format!("(↦ 0 {} {})", shifted_arg, self.body).parse().unwrap();

        let beta: PatternAst<LeanExpr> = if !arg_bvars.is_empty() || body_bvars.iter().any(|b| *b != 0) {
            format!("(↑ - 1 0 {})", sub).parse().unwrap()
        } else {
            sub
        };

        let (id, _) = graph.union_instantiations(ast.unwrap(), &beta, subst, rule);
        vec![id]
    }
}