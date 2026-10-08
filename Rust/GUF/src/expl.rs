use crate::analysis::*;
use crate::proof::*;
use crate::util::*;

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
    let _proof = egraph.get_g_between(lhs_id, rhs_id).unwrap();
    // TODO: Convert the proof to egg's flat explanation format, once GUF provides this conversion.
    Err("GUF backend: equality saturation proved the goal, but GUF cannot produce explanations yet".to_string())
}
