use rs2::PVar;
use crate::analysis::*;
use crate::egraph::*;
use crate::proof::*;
use crate::rewrite::*;
use crate::util::*;

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("≡η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : PVar::from("?f") }})
}

pub fn eta_expansion_rw() -> LeanRewrite {
    rewrite!("≡η+"; "?e" => { EtaExpand { term : PVar::from("?e") }})
}

struct Eta {
    fun: PVar
}

impl Applier for Eta {

    fn apply_one(&self, graph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let fun_bvars = &graph.data(&subst[&self.fun]).loose_bvars;
        if fun_bvars.contains(&0) { return }

        let new_fun = if fun_bvars.is_empty() {
            format!("{}", self.fun)
        } else {
            format!("(↑ - 1 0 {})", self.fun)
        };

        union_instantiation(graph, from, &pat(&new_fun), subst, rule);
    }
}

struct EtaExpand {
    term: PVar
}

impl Applier for EtaExpand {

    fn apply_one(&self, graph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        // TODO: This does not respect primitive constructors.

        let term_bvars = &graph.data(&subst[&self.term]).loose_bvars;

        let new_term = if term_bvars.is_empty() {
            format!("{}", self.term)
        } else {
            format!("(↑ + 1 0 {})", self.term)
        };

        let expanded = format!("(λ _ (app {} (bvar 0)))", new_term);

        union_instantiation(graph, from, &pat(&expanded), subst, rule);
    }
}
