use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use rs2::*;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::proof::*;

// An e-graph together with the e-node with which each of its e-classes was created (indexed by
// e-class id), and the rewrite rules which justify its unions. This is the e-graph object handed
// to Lean.
pub struct LeanEGraphObj {
    pub egraph: LeanEGraph,
    pub enodes: Vec<LeanExpr>,
    pub rules:  RuleTable,
}

// A rewrite rule as it is used to justify a union: the union's e-classes are instances of `lhs` and
// `rhs` (for the same substitution), and `name` is the name by which Lean identifies the rule.
//
// Note: The same name can appear with different patterns, as custom appliers construct the `rhs`
//       depending on the e-graph (e.g. `≡β`, `↑bvar` or `≡+`).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct RuleEntry {
    pub name: Rc<str>,
    pub lhs:  LeanPattern,
    pub rhs:  LeanPattern,
}

// The rewrite rules justifying the unions of an e-graph, indexed by the ids used in `ProofObj::Rule`.
#[derive(Default)]
pub struct RuleTable {
    pub entries: Vec<RuleEntry>,
    ids:         HashMap<RuleEntry, RuleId>,
}

impl RuleTable {

    // Returns the id of the given entry, adding the entry to the table if it is not present yet.
    pub fn id_of(&mut self, entry: RuleEntry) -> RuleId {
        if let Some(id) = self.ids.get(&entry) { return *id }
        let id = self.entries.len();
        self.entries.push(entry.clone());
        self.ids.insert(entry, id);
        id
    }

    pub fn get(&self, id: RuleId) -> &RuleEntry {
        &self.entries[id]
    }
}

thread_local! {
    // The e-node with which each e-class of the e-graph under construction was created. As GUF
    // does not track this information, we record it in `LeanAnalysis::mk`.
    static ENODES: RefCell<Vec<LeanExpr>> = RefCell::new(vec![]);

    // The rewrite rules justifying the unions of the e-graph under construction. We record them in
    // `union_instantiations`.
    static RULES: RefCell<RuleTable> = RefCell::new(Default::default());
}

pub fn start_recording() {
    ENODES.take();
    RULES.take();
}

pub fn finish_recording(egraph: LeanEGraph) -> LeanEGraphObj {
    LeanEGraphObj { egraph, enodes: ENODES.take(), rules: RULES.take() }
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

// Returns the id of the rule with the given name and patterns in the rule table of the e-graph under
// construction, adding the rule to the table if it is not present yet.
pub fn rule_id(rule: &str, lhs: &LeanPattern, rhs: &LeanPattern) -> RuleId {
    let entry = RuleEntry { name: rule.into(), lhs: lhs.clone(), rhs: rhs.clone() };
    RULES.with_borrow_mut(|rules| rules.id_of(entry))
}

// The id of a rule whose name and patterns are the same for all of its applications, which is
// obtained (via `rule_id`) on first use. This avoids constructing and hashing the rule's entry for
// each application.
//
// Note: As the rule table is reset by `start_recording`, a `RuleIdCache` must not outlive the
//       e-graph for which it was first used.
#[derive(Default)]
pub struct RuleIdCache(Cell<Option<RuleId>>);

impl RuleIdCache {

    pub fn get(&self, rule: &str, lhs: &LeanPattern, rhs: &LeanPattern) -> RuleId {
        if let Some(id) = self.0.get() {
            debug_assert!(RULES.with_borrow(|rules| rules.entries.get(id).is_some_and(|entry|
                &*entry.name == rule && entry.lhs == *lhs && entry.rhs == *rhs
            )));
            return id
        }
        let id = rule_id(rule, lhs, rhs);
        self.0.set(Some(id));
        id
    }
}

// Analogous to `union_instantiations` in egg: instantiates `from` and `to` with `subst` and unions
// the resulting e-classes. The union is justified by an application of the given rule, which
// rewrites the term represented by the instance of `from` to the term represented by the instance
// of `to`. The rule is recorded in the rule table together with `from` and `to`.
pub fn union_instantiations(egraph: &mut LeanEGraph, from: &LeanPattern, to: &LeanPattern, subst: &LeanSubst, rule: &str) -> bool {
    let id = rule_id(rule, from, to);
    union_instantiations_by_id(egraph, from, to, subst, id)
}

// Like `union_instantiations`, but for a rule whose id was already obtained. The rule's entry in the
// rule table must have the patterns `from` and `to`.
//
// Note: We don't use `EGraph::union`, as it rebuilds the e-graph after every union. Instead (as in
//       egg), the e-graph is rebuilt once per iteration of equality saturation.
pub fn union_instantiations_by_id(egraph: &mut LeanEGraph, from: &LeanPattern, to: &LeanPattern, subst: &LeanSubst, rule: RuleId) -> bool {
    let justification = Proof::rule(rule);
    let from = instantiate(from, egraph, subst);
    let (proof, id) = instantiate(to, egraph, subst);
    // `justification⁻¹ * to` represents the same term as `from`.
    egraph.uf.union(from, (Proof::compose(&justification.inverse(), &proof), id))
}
