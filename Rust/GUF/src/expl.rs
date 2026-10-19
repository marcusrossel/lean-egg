use crate::analysis::*;
use crate::Symbol;
use crate::egraph::RuleTable;
use crate::proof::*;
use crate::util::*;
use crate::LeanExpr;
use std::collections::HashMap;
use std::rc::Rc;
use rs2::Analysis;

#[derive(Clone, Copy)]
pub enum ExplanationKind {
    None,
    SameEClass,
    EqTrue
}

impl ExplanationKind {
    pub fn to_c(self) -> u8 {
        match self {
            Self::None => 0,
            Self::SameEClass => 1,
            Self::EqTrue => 2,
        }
    }

    fn for_goal(
        egraph: &LeanEGraph, init_expr: LeanTerm, goal_expr: LeanTerm, init_id: PId, goal_id: PId
    ) -> Option<(ExplanationKind, LeanTerm, LeanTerm)> {
        if egraph.find(init_id).1 == egraph.find(goal_id).1 {
            return Some((ExplanationKind::SameEClass, init_expr, goal_expr))
        }

        let eq_expr = term(&format!("(= {:?} {:?})", init_expr, goal_expr));
        let true_expr = term("(const \"True\")");
        let true_id = egraph.lookup_term(&true_expr).unwrap();

        // Note: `lookup_term` does not necessarily return canonical ids.
        if egraph.lookup_term(&eq_expr).map(|x| egraph.find(x).1) == Some(egraph.find(true_id).1) {
            return Some((ExplanationKind::EqTrue, eq_expr, true_expr))
        }

        None
    }
}

pub fn mk_explanation(
    egraph: &LeanEGraph, rules: &RuleTable, init_expr: LeanTerm, goal_expr: LeanTerm, init_id: PId, goal_id: PId
) -> (ExplanationKind, String) {
    match ExplanationKind::for_goal(egraph, init_expr, goal_expr, init_id, goal_id) {
        None => (ExplanationKind::None, "".to_string()),
        Some((kind, lhs, rhs)) => match explain_equivalence(egraph, rules, &lhs, &rhs) {
            Ok(expl) => (kind, expl),
            Err(msg) => (ExplanationKind::None, msg)
        }
    }
}

// Analogous to `explain_equivalence(lhs, rhs).get_flat_string()` in egg.
// The `rules` map the ids in `ProofObj::Rule` to the corresponding rule names and patterns.
fn explain_equivalence(egraph: &LeanEGraph, rules: &RuleTable, lhs: &LeanTerm, rhs: &LeanTerm) -> Result<String, String> {
    let lhs_id = egraph.lookup_term(lhs).unwrap();
    let rhs_id = egraph.lookup_term(rhs).unwrap();
    // The proof `p` with `p * lhs_id = rhs_id`, that is, a proof of `lhs = rhs`.
    let proof = egraph.get_g_between(lhs_id, rhs_id).unwrap();

    let mut mvar_counter = 0;
    let mut umap = UnifyMap::default();

    let e = eval(&proof, &mut mvar_counter, &mut umap, rules);
    unify(e.first(), &explify(lhs), &mut umap);
    unify(&e.last, &explify(rhs), &mut umap);
    let e = guess_mvars(e);

    Ok(stringify(&e))
}

struct Expl {
    vec: Vec<(LeanPattern, ExplStep)>,
    last: LeanPattern,
}

impl Expl {
    pub fn first(&self) -> &LeanPattern {
        self.vec.first().map(|(x, _)| x).unwrap_or_else(|| &self.last)
    }
}

type ExplStep = (/*rule id*/ Rc<str>, /*pos*/ Vec<usize>); // last index in vector is innermost index.

type UnifyMap = HashMap<Symbol, LeanPattern>;

// will panic if it can't unify.
fn unify(l: &LeanPattern, r: &LeanPattern, umap: &mut UnifyMap) {
    match (l, r) {
        (LeanPattern::PVar(p), t)|(t, LeanPattern::PVar(p)) => {
            umap.insert(*p, t.clone());
        },
        (LeanPattern::Node(n1, cs1), LeanPattern::Node(n2, cs2)) => {
            assert!(LeanAnalysis::matches(&n1, &n2));
            for (c1, c2) in cs1.iter().zip(cs2.iter()) {
                unify(c1, c2, umap);
            }
        },
        (LeanPattern::G(..),_)|(_,LeanPattern::G(..)) => unreachable!(),
    }
}

fn eval_trans(e2: Expl, e1: Expl, mvar_counter: &mut usize, umap: &mut UnifyMap, rules: &RuleTable) -> Expl {
    unify(&e1.last, e2.first(), umap);
    Expl {
        vec: e1.vec.iter().cloned().chain(e2.vec.iter().cloned()).collect(),
        last: e2.last.clone(),
    }
}

fn eval(p: &Proof, mvar_counter: &mut usize, umap: &mut UnifyMap, rules: &RuleTable) -> Expl {
    match &*p.0 {
        ProofObj::Refl => Expl {
            vec: Vec::new(),
            last: LeanPattern::PVar(fresh_mvar(mvar_counter)),
        },
        ProofObj::Sym(p) => {
            let e = eval(p, mvar_counter, umap, rules);
            let n = e.vec.len();
            Expl {
                vec: (0..n).rev().map(|i| {
                    let node = if i == 0 { &e.last } else { &e.vec[i-1].0 }.clone();
                    let edge = e.vec[i].1.clone();
                    (node, edge)
                }).collect(),
                last: e.first().clone(),
            }
        },
        ProofObj::Trans(p2, p1) => {
            let e1 = eval(p1, mvar_counter, umap, rules);
            let e2 = eval(p2, mvar_counter, umap, rules);
            eval_trans(e2, e1, mvar_counter, umap, rules)
        },
        ProofObj::Congr(sid, children) => {
            let mut cs = Vec::new();
            for (i, c) in children.iter().enumerate() {
                let inner = eval(c, mvar_counter, umap, rules);
                let wrapped = wrap(inner, mvar_counter, i, children.len(), *sid);
                cs.push(wrapped);
            }
            let mut total = cs.pop().unwrap();
            // TODO: is the order of eval correct here?
            for x in cs.into_iter().rev() {
                total = eval_trans(total, x, mvar_counter, umap, rules);
            }
            total
        },
        ProofObj::Rule(rule_id) => {
            let entry = rules.get(*rule_id).clone();
            Expl {
                vec: vec![(entry.lhs, (entry.name, Vec::new()))],
                last: entry.rhs,
            }
        },
    }
}

fn wrap(mut e: Expl, mvar_counter: &mut usize, i: usize, arity: usize, si: SymbolId) -> Expl {
    let l: Box<[LeanPattern]> = (0..arity).map(|_| LeanPattern::PVar(fresh_mvar(mvar_counter))).collect();
    for p in e.vec.iter_mut().map(|(_, (_, p))| p) {
        p.push(i);
    }
    for t in e.vec.iter_mut().map(|(x, _)| x).chain(std::iter::once(&mut e.last)) {
        let node = si.build(vec![nil(); arity].into());
        let mut children = l.clone();
        children[i] = t.clone();
        *t = LeanTerm::Node(node, children);
    }
    e
}

fn fresh_mvar(mvar_counter: &mut usize) -> Symbol {
    let x = *mvar_counter;
    *mvar_counter += 1;
    Symbol::from(format!("fresh{x}"))
}

// remove all remaining mvars by instantiating them with some guessed value.
fn guess_mvars(expl: Expl) -> Expl {
    todo!()
}

fn explify(l: &LeanTerm) -> LeanPattern {
    l.clone()
}

fn stringify(expl: &Expl) -> String {
    todo!()
}
