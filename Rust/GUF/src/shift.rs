use rs2::PVar;
use crate::analysis::*;
use crate::egraph::*;
use crate::proof::*;
use crate::rewrite::*;
use crate::util::*;

struct BVarShift {
    dir:      PVar,
    offset:   PVar,
    cutoff:   PVar,
    bvar_idx: PVar
}

impl Applier for BVarShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let dir_is_up = egraph.data(&subst[&self.dir]).dir_val.unwrap();
        let offset    = egraph.data(&subst[&self.offset]).nat_val.unwrap();
        let cutoff    = egraph.data(&subst[&self.cutoff]).nat_val.unwrap();
        let bvar_idx  = egraph.data(&subst[&self.bvar_idx]).nat_val.unwrap();

        let new_idx = if bvar_idx < cutoff {
            bvar_idx
        } else if dir_is_up {
            bvar_idx + offset
        } else if offset <= bvar_idx {
            bvar_idx - offset
        } else {
            // If `offset > bvar_idx`, this shift was "not intended", so we just don't do it.
            return
        };
        let new = format!("(bvar {})", new_idx);

        union_instantiation(egraph, from, &pat(&new), subst, rule);
    }
}

struct BasicShift {
    ctor:   String,
    dir:    PVar,
    offset: PVar,
    cutoff: PVar,
    left:   PVar,
    right:  PVar
}

impl Applier for BasicShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let left_bvars  = &egraph.data(&subst[&self.left]).loose_bvars;
        let right_bvars = &egraph.data(&subst[&self.right]).loose_bvars;
        let cutoff      = &egraph.data(&subst[&self.cutoff]).nat_val.unwrap();

        let shifted_left = if left_bvars.iter().all(|b| b < cutoff) {
            format!("{}", self.left)
        } else {
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.left)
        };

        let shifted_right = if right_bvars.iter().all(|b| b < cutoff) {
            format!("{}", self.right)
        } else {
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.right)
        };

        let shifted_app = format!("({} {} {})", self.ctor, shifted_left, shifted_right);
        union_instantiation(egraph, from, &pat(&shifted_app), subst, rule);
    }
}

struct BinderShift {
    binder:   String,
    dir:      PVar,
    offset:   PVar,
    cutoff:   PVar,
    domain:   PVar,
    body:     PVar
}

impl Applier for BinderShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        let domain_bvars = &egraph.data(&subst[&self.domain]).loose_bvars;
        let body_bvars   = &egraph.data(&subst[&self.body]).loose_bvars;
        let cutoff       = &egraph.data(&subst[&self.cutoff]).nat_val.unwrap();

        let shifted_domain = if domain_bvars.iter().all(|b| b < cutoff) {
            format!("{}", self.domain)
        } else {
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.domain)
        };

        let shifted_body = if body_bvars.iter().all(|b| b <= cutoff) {
            format!("{}", self.body)
        } else {
            format!("(↑ {} {} {} {})", self.dir, self.offset, cutoff + 1, self.body)
        };

        let shifted_binder = format!("({} {} {})", self.binder, shifted_domain, shifted_body);
        union_instantiation(egraph, from, &pat(&shifted_binder), subst, rule);
    }
}

// We try to reduce the number of introduced shifting rules á la
// https://pldi23.sigplan.org/details/egraphs-2023-papers/12/Optimizing-Beta-Reduction-in-E-Graphs
// TODO: Is this ok when using intersection semantics?
pub fn shift_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(rewrite!("↑bvar";  "(↑ ?d ?o ?c (bvar ?b))"   => { BVarShift   { dir: PVar::from("?d"), offset: PVar::from("?o"), cutoff: PVar::from("?c"), bvar_idx: PVar::from("?b") }}));
    rws.push(rewrite!("↑app";   "(↑ ?d ?o ?c (app ?a ?b))" => { BasicShift  { ctor: "app".to_string(), dir: PVar::from("?d"), offset: PVar::from("?o"), cutoff: PVar::from("?c"), left:   PVar::from("?a"), right: PVar::from("?b") }}));
    rws.push(rewrite!("↑=";     "(↑ ?d ?o ?c (= ?a ?b))"   => { BasicShift  { ctor: "=".to_string(),   dir: PVar::from("?d"), offset: PVar::from("?o"), cutoff: PVar::from("?c"), left:   PVar::from("?a"), right: PVar::from("?b") }}));
    rws.push(rewrite!("↑λ";     "(↑ ?d ?o ?c (λ ?a ?b))"   => { BinderShift { binder: "λ".to_string(), dir: PVar::from("?d"), offset: PVar::from("?o"), cutoff: PVar::from("?c"), domain: PVar::from("?a"), body:  PVar::from("?b") }}));
    rws.push(rewrite!("↑∀";     "(↑ ?d ?o ?c (∀ ?a ?b))"   => { BinderShift { binder: "∀".to_string(), dir: PVar::from("?d"), offset: PVar::from("?o"), cutoff: PVar::from("?c"), domain: PVar::from("?a"), body:  PVar::from("?b") }}));
    rws.push(rewrite!("↑fvar";  "(↑ ?d ?o ?c (fvar ?x))"   => "(fvar ?x)"));
    rws.push(rewrite!("↑mvar";  "(↑ ?d ?o ?c (mvar ?x))"   => "(mvar ?x)"));
    rws.push(rewrite!("↑sort";  "(↑ ?d ?o ?c (sort ?x))"   => "(sort ?x)"));
    // TODO: "↑const" - how do we match an unknown number of level arguments?
    rws.push(rewrite!("↑lit";   "(↑ ?d ?o ?c (lit ?x))"    => "(lit ?x)"));
    // TODO: We don't propagate shifts over erased terms at the moment.
    rws.push(rewrite!("↑proof"; "(↑ ?d ?o ?c (proof ?x))"  => "(proof ?x)"));
    rws.push(rewrite!("↑inst";  "(↑ ?d ?o ?c (inst ?x))"   => "(inst ?x)"));
    rws.push(rewrite!("↑_";     "(↑ ?d ?o ?c _)"           => "_"));
    // Note: We don't handle the propagation of shifts over facts, as a shift should never even be
    //       applied to a fact.
    rws
}
