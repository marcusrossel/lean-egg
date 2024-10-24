use std::time::Instant;
use std::collections::HashMap;
use slotted_egraphs::*;
use crate::result::*;
use crate::analysis::*;
use crate::beta::*;
use crate::eta::*;
use crate::levels::*;
use crate::nat_lit::*;
use crate::reporting::*;
use crate::rewrite::*;

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
    allow_unsat_conditions: bool
}

pub fn explain_congr(
    init: String, goal: String, rw_templates: Vec<RewriteTemplate>, facts: Vec<(String, String)>, 
    guides: Vec<String>, cfg: Config, _viz_path: Option<String>
) -> Result<(String, LeanEGraph, Report), Error> {    
    let mut egraph: LeanEGraph = EGraph::new();
    
    // TODO:
    // egraph = egraph.with_explanations_enabled();
    // if !cfg.optimize_expl { egraph = egraph.without_explanation_length_optimization() }

    let init_expr = RecExpr::parse(&init).map_err(|err| {
        Error::Init(format!("Failed to parse lhs of goal: {:?}\n\n  {}", err, init).to_string())
    })?;
    let goal_expr = RecExpr::parse(&goal).map_err(|err| {
        Error::Goal(format!("Failed to parse rhs of goal: {:?}\n\n  {}", err, goal).to_string())
    })?;
    let init_id = egraph.add_expr(init_expr.clone());
    let goal_id = egraph.add_expr(goal_expr.clone());

    for guide in guides {
        let expr = RecExpr::parse(&guide).map_err(|err| {
            Error::Guide(format!("Failed to parse guide term: {:?}\n\n  {}", err, guide).to_string())
    })?;
        egraph.add_expr(expr);
    }

    let mut fact_map: HashMap<AppliedId, String> = Default::default();
    for (name, expr) in facts {
        let expr = RecExpr::parse(&expr).map_err(|err| {
            Error::Fact(format!("Failed to parse fact: {:?}\n\n  {}", err, expr).to_string())
        })?;
        let class = egraph.add_expr(expr);
        fact_map.insert(class, name);
    }

    let mut rws;
    match templates_to_rewrites(rw_templates, fact_map, cfg.allow_unsat_conditions) {
        Ok(r)    => rws = r,
        Err(err) => return Err(Error::Rewrite(err.to_string()))
    }
    if cfg.gen_nat_lit_rws { rws.append(&mut nat_lit_rws()) }
    if cfg.gen_eta_rw      { rws.push(eta_reduction_rw()) }
    if cfg.gen_beta_rw     { rws.push(beta_reduction_rw()) }
    if cfg.gen_level_rws   { rws.append(&mut level_rws()) }

    let start_time = Instant::now();
    let mut iter_count = 0;
    let mut node_count = egraph.total_number_of_nodes();
    let stop_reason: StopReason;
    loop {
        apply_rewrites(&mut egraph, &rws);
        
        if egraph.eq(&init_id, &goal_id) {
            stop_reason = StopReason::Other;
            break
        }

        if start_time.elapsed().as_secs() >= cfg.time_limit.try_into().unwrap() {
            stop_reason = StopReason::TimeLimit;
            break
        }

        if iter_count >= cfg.iter_limit {
            stop_reason = StopReason::IterationLimit;
            break
        }

        if node_count >= cfg.node_limit {
            stop_reason = StopReason::NodeLimit;
            break
        }

        let new_count = egraph.total_number_of_nodes();
        if new_count == node_count {
            stop_reason = StopReason::Saturated;
            break
        }
        
        iter_count += 1;
        node_count = new_count;
    }

    let report = Report {
        iterations: iter_count,
        stop_reason: stop_reason,
        egraph_nodes: egraph.total_number_of_nodes(),
        egraph_classes: 0, // TODO: `egraph.classes` is public in 0.0.4
        total_time: start_time.elapsed().as_secs_f64()
    };

    if egraph.eq(&init_id, &goal_id) {
        let expl = egraph.explain_equivalence(init_expr, goal_expr).to_string(&egraph);
        Ok((expl, egraph, report))
    } else {
        Ok(("".to_string(), egraph, report))
    }
}