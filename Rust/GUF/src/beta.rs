use rs2::PVar;
use crate::analysis::*;
use crate::egraph::*;
use crate::proof::*;
use crate::rewrite::*;
use crate::util::*;

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("≡β"; "(app (λ ?t ?b) ?a)" => { Beta { body : PVar::from("?b"), arg : PVar::from("?a") }})
}

struct Beta {
    body: PVar,
    arg:  PVar
}

impl Applier for Beta {

    fn apply_one(&self, graph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let arg_bvars = &graph.data(&subst[&self.arg]).loose_bvars;
        let body_bvars = &graph.data(&subst[&self.body]).loose_bvars;

        let shifted_arg = if arg_bvars.is_empty() {
            format!("{}", self.arg)
        } else {
            format!("(↑ + 1 0 {})", self.arg)
        };

        let sub = format!("(↦ 0 {} {})", shifted_arg, self.body);

        let beta = if !arg_bvars.is_empty() || body_bvars.iter().any(|b| *b != 0) {
            format!("(↑ - 1 0 {})", sub)
        } else {
            sub
        };

        union_instantiation(graph, from, &pat(&beta), subst, rule);
    }
}
