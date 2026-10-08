use rs2::PVar;
use crate::analysis::*;
use crate::egraph::*;
use crate::proof::*;
use crate::rewrite::*;
use crate::util::*;

struct BVarSubst {
    from_idx: PVar,
    to:       PVar,
    bvar_idx: PVar
}

impl Applier for BVarSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let from_idx = egraph.data(&subst[&self.from_idx]).nat_val.unwrap();
        let bvar_idx = egraph.data(&subst[&self.bvar_idx]).nat_val.unwrap();

        let new = if from_idx == bvar_idx {
            format!("{}", self.to)
        } else {
            format!("(bvar {})", bvar_idx)
        };

        union_instantiation(egraph, from, &pat(&new), subst, rule);
    }
}

struct BasicSubst {
    ctor:     String,
    from_idx: PVar,
    to:       PVar,
    left:     PVar,
    right:    PVar
}

impl Applier for BasicSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let from_idx    = egraph.data(&subst[&self.from_idx]).nat_val.unwrap();
        let left_bvars  = &egraph.data(&subst[&self.left]).loose_bvars;
        let right_bvars = &egraph.data(&subst[&self.right]).loose_bvars;

        let new_left = if left_bvars.contains(&from_idx) {
            format!("(↦ {} {} {})", self.from_idx, self.to, self.left)
        } else {
            format!("{}", self.left)
        };

        let new_right = if right_bvars.contains(&from_idx) {
            format!("(↦ {} {} {})", self.from_idx, self.to, self.right)
        } else {
            format!("{}", self.right)
        };

        let new_expr = format!("({} {} {})", self.ctor, new_left, new_right);
        union_instantiation(egraph, from, &pat(&new_expr), subst, rule);
    }
}

struct BinderSubst {
    binder:   String,
    from_idx: PVar,
    to:       PVar,
    domain:   PVar,
    body:     PVar
}

impl Applier for BinderSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let from_idx     = egraph.data(&subst[&self.from_idx]).nat_val.unwrap();
        let to_bvars     = &egraph.data(&subst[&self.to]).loose_bvars;
        let domain_bvars = &egraph.data(&subst[&self.domain]).loose_bvars;
        let body_bvars   = &egraph.data(&subst[&self.body]).loose_bvars;

        let new_domain = if domain_bvars.contains(&from_idx) {
            format!("(↦ {} {} {})", self.from_idx, self.to, self.domain)
        } else {
            format!("{}", self.domain)
        };

        let new_body = if body_bvars.contains(&(from_idx + 1)) {
            let to_shifted = if to_bvars.is_empty() {
                format!("{}", self.to)
            } else {
                format!("(↑ + 1 0 {})", self.to)
            };
            format!("(↦ {} {} {})", from_idx + 1, to_shifted, self.body)
        } else {
            format!("{}", self.body)
        };

        let new_binder = format!("({} {} {})", self.binder, new_domain, new_body);
        union_instantiation(egraph, from, &pat(&new_binder), subst, rule);
    }
}

// We try to reduce the number of introduced substitution rules á la
// https://pldi23.sigplan.org/details/egraphs-2023-papers/12/Optimizing-Beta-Reduction-in-E-Graphs
// TODO: Is this ok when using intersection semantics?
pub fn subst_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(rewrite!("↦bvar";  "(↦ ?f ?t (bvar ?b))"   => { BVarSubst   { from_idx : PVar::from("?f"), to : PVar::from("?t"), bvar_idx : PVar::from("?b") }}));
    rws.push(rewrite!("↦app";   "(↦ ?f ?t (app ?a ?b))" => { BasicSubst  { ctor: "app".to_string(), from_idx : PVar::from("?f"), to : PVar::from("?t"), left   : PVar::from("?a"), right : PVar::from("?b") }}));
    rws.push(rewrite!("↦=";     "(↦ ?f ?t (= ?a ?b))"  => { BasicSubst  { ctor: "=".to_string(),   from_idx : PVar::from("?f"), to : PVar::from("?t"), left   : PVar::from("?a"), right : PVar::from("?b") }}));
    rws.push(rewrite!("↦λ";     "(↦ ?f ?t (λ ?a ?b))"   => { BinderSubst { binder: "λ".to_string(), from_idx : PVar::from("?f"), to : PVar::from("?t"), domain : PVar::from("?a"), body  : PVar::from("?b") }}));
    rws.push(rewrite!("↦∀";     "(↦ ?f ?t (∀ ?a ?b))"   => { BinderSubst { binder: "∀".to_string(), from_idx : PVar::from("?f"), to : PVar::from("?t"), domain : PVar::from("?a"), body  : PVar::from("?b") }}));
    rws.push(rewrite!("↦fvar";  "(↦ ?f ?t (fvar ?x))"   => "(fvar ?x)"));
    rws.push(rewrite!("↦mvar";  "(↦ ?f ?t (mvar ?x))"   => "(mvar ?x)"));
    rws.push(rewrite!("↦sort";  "(↦ ?f ?t (sort ?x))"   => "(sort ?x)"));
    // TODO: "↦const" - how do we match an unknown number of level arguments?
    rws.push(rewrite!("↦lit";   "(↦ ?f ?t (lit ?x))"    => "(lit ?x)"));
    // TODO: We don't propagate substitutions over erased terms at the moment.
    rws.push(rewrite!("↦proof"; "(↦ ?f ?t (proof ?x))"  => "(proof ?x)"));
    rws.push(rewrite!("↦inst";  "(↦ ?f ?t (inst ?x))"   => "(inst ?x)"));
    rws.push(rewrite!("↦_";     "(↦ ?f ?t _)"           => "_"));
    // Note: We don't handle the propagation of substitutions over facts, as a substitution should
    //       never even be applied to a fact.
    rws
}
