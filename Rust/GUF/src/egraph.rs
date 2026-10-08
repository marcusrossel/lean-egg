use std::cell::RefCell;
use rs2::*;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::proof::*;

// An e-graph together with the e-node with which each of its e-classes was created (indexed by
// e-class id). This is the e-graph object handed to Lean.
pub struct LeanEGraphObj {
    pub egraph: LeanEGraph,
    pub enodes: Vec<LeanExpr>,
}

thread_local! {
    // The e-node with which each e-class of the e-graph under construction was created. As GUF
    // does not track this information, we record it in `LeanAnalysis::mk`.
    static ENODES: RefCell<Vec<LeanExpr>> = RefCell::new(vec![]);
}

pub fn start_recording_enodes() {
    ENODES.take();
}

pub fn finish_recording_enodes() -> Vec<LeanExpr> {
    ENODES.take()
}

// GUF calls `Analysis::mk` with a fresh id exactly when it creates a new e-class.
pub fn record_enode(enode: &LeanExpr, id: Id) {
    ENODES.with_borrow_mut(|enodes| if id.0 == enodes.len() { enodes.push(enode.clone()) })
}

pub fn with_recorded_enodes<R>(f: impl FnOnce(&[LeanExpr]) -> R) -> R {
    ENODES.with_borrow(|enodes| f(enodes))
}

// Analogous to `id_to_expr` in egg with explanations enabled: returns the term with which the given
// e-class was created.
pub fn id_to_expr(enodes: &[LeanExpr], id: Id) -> LeanTerm {
    let enode = &enodes[id.0];
    let children = enode.children().iter().map(|(_, child)| id_to_expr(enodes, *child)).collect();
    Pattern::Node(enode.without_children(), children)
}

// Instantiates the given pattern with the terms of the e-classes in the given substitution.
pub fn instantiate_term(pat: &LeanPattern, enodes: &[LeanExpr], subst: &LeanSubst) -> LeanTerm {
    match pat {
        Pattern::PVar(var)          => id_to_expr(enodes, subst[var].1),
        Pattern::Node(enode, pats) => Pattern::Node(enode.clone(), pats.iter().map(|p| instantiate_term(p, enodes, subst)).collect()),
        Pattern::G(..)              => unreachable!("patterns are not proof-annotated")
    }
}

// The e-nodes in the e-class of `x` (cf. `egraph[x].nodes` in egg), where `x` has to have been
// canonical when the e-graph was last rebuilt.
pub fn class_nodes(x: Id, egraph: &LeanEGraph) -> Vec<LeanExpr> {
    egraph.nodes.get(&x).into_iter().flatten()
        .map(|idx| egraph.hashcons.get_index(*idx).unwrap().0.clone())
        .collect()
}

// Unions the e-classes of `from` and `to`, justified by an application of the given rule, which
// rewrites the term represented by `from` to the term represented by `to`.
//
// Note: We don't use `EGraph::union`, as it rebuilds the e-graph after every union. Instead (as in
//       egg), the e-graph is rebuilt once per iteration of equality saturation.
pub fn union_justified(egraph: &mut LeanEGraph, from: PId, to: PId, rule: &str) -> bool {
    let justification = Proof::rule(rule, from.clone(), to.clone());
    // `justification⁻¹ * to` represents the same term as `from`.
    let (proof, id) = to;
    egraph.uf.union(from, (Proof::compose(&justification.inverse(), &proof), id))
}

// Analogous to `union_instantiations` in egg, except that the left-hand side is already given as
// an (instantiated) e-class.
pub fn union_instantiation(egraph: &mut LeanEGraph, from: PId, to: &LeanPattern, subst: &LeanSubst, rule: &str) -> bool {
    let to = instantiate(to, egraph, subst);
    union_justified(egraph, from, to, rule)
}

// Analogous to `union_instantiations` in egg with an empty substitution.
pub fn union_terms(egraph: &mut LeanEGraph, from: &LeanTerm, to: &LeanTerm, rule: &str) -> bool {
    let from = add_expr(from, egraph);
    union_instantiation(egraph, from, to, &LeanSubst::new(), rule)
}
