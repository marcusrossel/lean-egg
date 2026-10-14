use crate::analysis::*;
use crate::proof::*;
use crate::util::*;
use crate::LeanExpr;
use std::collections::HashMap;
use std::rc::Rc;

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
    egraph: &LeanEGraph, init_expr: LeanTerm, goal_expr: LeanTerm, init_id: PId, goal_id: PId
) -> (ExplanationKind, String) {
    match ExplanationKind::for_goal(egraph, init_expr, goal_expr, init_id, goal_id) {
        None => (ExplanationKind::None, "".to_string()),
        Some((kind, lhs, rhs)) => match explain_equivalence(egraph, &lhs, &rhs) {
            Ok(expl) => (kind, expl),
            Err(msg) => (ExplanationKind::None, msg)
        }
    }
}

// Analogous to `explain_equivalence(lhs, rhs).get_flat_string()` in egg.
fn explain_equivalence(egraph: &LeanEGraph, lhs: &LeanTerm, rhs: &LeanTerm) -> Result<String, String> {
    let lhs_id = egraph.lookup_term(lhs).unwrap();
    let rhs_id = egraph.lookup_term(rhs).unwrap();
    // The proof `p` with `p * lhs_id = rhs_id`, that is, a proof of `lhs = rhs`.
    let proof = egraph.get_g_between(lhs_id, rhs_id).unwrap();

    let mut mvar_counter = 0;
    let mut umap = UnifyMap::default();

    let e = eval(&proof, &mut mvar_counter, &mut umap);
    unify(e.first(), &explify(lhs), &mut umap);
    unify(&e.last, &explify(rhs), &mut umap);
    let e = guess_mvars(e);

    Ok(stringify(&e))
}

struct Expl {
    vec: Vec<(ExplTerm, ExplStep)>,
    last: ExplTerm,
}

impl Expl {
    pub fn first(&self) -> &ExplTerm {
        self.vec.first().map(|(x, _)| x).unwrap_or_else(|| &self.last)
    }
}

type MVar = usize;

// ExplTerm are terms with mvars.
#[derive(Clone)]
enum ExplTerm {
    Node(LeanExpr, Box<[ExplTerm]>), // all Proofs in that LeanExpr are going to be refl.
    MVar(MVar),
}

type ExplStep = (/*rule id*/ Rc<str>, /*pos*/ Vec<usize>); // last index in vector is innermost index.

type UnifyMap = HashMap<MVar, ExplTerm>;

// will panic if it can't unify.
fn unify(l: &ExplTerm, r: &ExplTerm, umap: &mut UnifyMap) {
    todo!()
}

fn eval(p: &Proof, mvar_counter: &mut usize, umap: &mut UnifyMap) -> Expl {
    match &*p.0 {
        ProofObj::Refl => Expl {
            vec: Vec::new(),
            last: ExplTerm::MVar(fresh_mvar(mvar_counter)),
        },
        ProofObj::Sym(p) => {
            let e = eval(p, mvar_counter, umap);
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
            let e1 = eval(p1, mvar_counter, umap);
            let e2 = eval(p2, mvar_counter, umap);
            unify(&e1.last, e2.first(), umap);
            Expl {
                vec: e1.vec.iter().cloned().chain(e2.vec.iter().cloned()).collect(),
                last: e2.last.clone(),
            }
        },
        ProofObj::Congr(sid, children) => todo!(),
        ProofObj::Rule(rule_name) => todo!(),
    }
}

fn fresh_mvar(mvar_counter: &mut usize) -> MVar {
    let x = *mvar_counter;
    *mvar_counter += 1;
    x
}

// remove all remaining mvars by instantiating them with some guessed value.
fn guess_mvars(expl: Expl) -> Expl {
    todo!()
}

fn explify(l: &LeanTerm) -> ExplTerm {
    todo!()
}

fn stringify(expl: &Expl) -> String {
    todo!()
}
