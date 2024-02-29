use egg::*;
use crate::result::*;
use crate::analysis::*;
use crate::nat_lit::*;

pub fn explain_congr(init: String, goal: String, rws: Vec<LeanRewrite>, optimize_expl: bool, gen_nat_lit_rws: bool, viz_path: Option<String>) -> Res<String> {
    let mut egraph: LeanEGraph = Default::default();
    egraph = egraph.with_explanations_enabled();
    if !optimize_expl { egraph = egraph.without_explanation_length_optimization() }
    let init_expr = init.parse().map_err(|e : RecExprParseError<_>| Error::Init(e.to_string()))?;
    let goal_expr = goal.parse().map_err(|e : RecExprParseError<_>| Error::Goal(e.to_string()))?;
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);
    let mut rws = rws;
    if gen_nat_lit_rws { rws.append(&mut nat_lit_rws()) }
    let mut runner = Runner::default()
        .with_egraph(egraph)
        .with_hook(move |runner| {
            if let Some(path) = &viz_path {
                runner.egraph.dot().to_dot(format!("{}/{}.dot", path, runner.iterations.len())).unwrap();
            }
            if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
                Err("search complete".to_string())
            } else {
                Ok(())
            }
        })
        .run(&rws);
    if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
        let mut expl = runner.explain_equivalence(&init_expr, &goal_expr);
        let expl_str = expl.get_flat_string();
        Ok(expl_str)
    } else {
        Err(Error::Failed)
    }
}