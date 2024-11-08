use std::time::Duration;
use std::collections::HashMap;
use egg::*;
use crate::result::*;
use crate::analysis::*;
use crate::beta::*;
use crate::eta::*;
use crate::levels::*;
use crate::nat_lit::*;
use crate::rewrite::*;
use crate::shift::*;
use crate::subst::*;

#[repr(C)]
pub struct Config {
    optimize_expl:          bool,
    time_limit:             usize,
    node_limit:             usize,
    iter_limit:             usize, 
    gen_nat_lit_rws:        bool, 
    gen_eta_rw:             bool,
    gen_beta_rw:            bool,
    gen_level_rws:          bool,
    shapes:                 bool,
    block_invalid_matches:  bool,
    shift_captured_bvars:   bool,
    union_semantics:        bool,
    allow_unsat_conditions: bool
}

pub fn explain_congr(init: String, goal: String, rw_templates: Vec<RewriteTemplate>, facts: Vec<(String, String)>, guides: Vec<String>, cfg: Config, viz_path: Option<String>) -> Result<(String, LeanEGraph, Report), Error> {    
    let analysis = LeanAnalysis { union_semantics: cfg.union_semantics };
    let mut egraph: LeanEGraph = EGraph::new(analysis);
    egraph = egraph.with_explanations_enabled();
    if !cfg.optimize_expl { egraph = egraph.without_explanation_length_optimization() }

    let init_expr = init.parse().map_err(|e : RecExprParseError<_>| Error::Init(e.to_string()))?;
    let goal_expr = goal.parse().map_err(|e : RecExprParseError<_>| Error::Goal(e.to_string()))?;
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);

    for guide in guides {
        let expr = guide.parse().map_err(|e : RecExprParseError<_>| Error::Guide(e.to_string()))?;
        egraph.add_expr(&expr);
    }

    let mut fact_map: HashMap<Id, String> = Default::default();
    for (name, expr) in facts {
        let expr = expr.parse().map_err(|e : RecExprParseError<_>| Error::Fact(e.to_string()))?;
        let class = egraph.add_expr(&expr);
        fact_map.insert(class, name);
    }

    let mut rws;
    match templates_to_rewrites(rw_templates, fact_map, cfg.block_invalid_matches, cfg.shift_captured_bvars, cfg.allow_unsat_conditions) {
        Ok(r)    => rws = r,
        Err(err) => return Err(Error::Rewrite(err.to_string()))
    }
    if cfg.gen_nat_lit_rws { rws.append(&mut nat_lit_rws(cfg.shapes)) }
    if cfg.gen_eta_rw      { rws.push(eta_reduction_rw()) }
    if cfg.gen_beta_rw     { rws.push(beta_reduction_rw()) }
    if cfg.gen_level_rws   { rws.append(&mut level_rws()) }
    // TODO: Only add these rws if on of the following is active: beta, eta, bvar index correction. Anything else?
    rws.append(&mut subst_rws());
    rws.append(&mut shift_rws());

    let mut runner = Runner::default()
        .with_egraph(egraph)
        .with_time_limit(Duration::from_secs(cfg.time_limit.try_into().unwrap()))
        .with_node_limit(cfg.node_limit)
        .with_iter_limit(cfg.iter_limit)
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

    let report = runner.report();

    if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
        let mut expl = runner.explain_equivalence(&init_expr, &goal_expr);
        let expl_str = expl.get_flat_string();
        Ok((expl_str, runner.egraph, report))
    } else {
        Ok(("".to_string(), runner.egraph, report))
    }
}