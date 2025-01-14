use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

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
        egraph: &LeanEGraph, init_expr: RecExpr<LeanExpr>, goal_expr: RecExpr<LeanExpr>, init_id: Id, 
        goal_id: Id
    ) -> (ExplanationKind, RecExpr<LeanExpr>, RecExpr<LeanExpr>) {
        if egraph.find(init_id) == egraph.find(goal_id) {
            return (ExplanationKind::SameEClass, init_expr, goal_expr)
        }

        let eq_expr = format!("(= {} {})", init_expr, goal_expr).parse().unwrap();
        let true_expr = "(const \"True\")".parse().unwrap();
        let true_id = egraph.lookup_expr(&true_expr).unwrap();
        
        // Note: `lookup_expr` canonicalizes ids.
        if egraph.lookup_expr(&eq_expr) == Some(true_id) {
            return (ExplanationKind::EqTrue, eq_expr, true_expr)
        }

        (ExplanationKind::None, RecExpr::default(), RecExpr::default())
    }
}

pub fn mk_explanation(
    egraph: &mut LeanEGraph, init_expr: RecExpr<LeanExpr>, goal_expr: RecExpr<LeanExpr>, init_id: Id, 
    goal_id: Id
) -> (ExplanationKind, String) {
    let (kind, lhs, rhs) = ExplanationKind::for_goal(egraph, init_expr, goal_expr, init_id, goal_id);
    let expl: String;
    match kind {
        ExplanationKind::None => expl = "".to_string(),
        ExplanationKind::EqTrue | ExplanationKind::SameEClass => {
            expl = egraph.explain_equivalence(&lhs, &rhs).get_flat_string()
        }
    }

    (kind, expl)
}
