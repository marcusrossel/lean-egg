use std::time::Duration;
use std::collections::HashMap;
use std::ffi::c_void;
use egg::*;
use crate::result::*;
use crate::analysis::*;
use crate::beta::*;
use crate::eta::*;
use crate::lean_expr::*;
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
    nat_lit:                bool, 
    eta:                    bool,
    eta_expand:             bool,
    beta:                   bool,
    levels:                 bool,
    shapes:                 bool,
    block_invalid_matches:  bool,
    shift_captured_bvars:   bool,
    union_semantics:        bool,
    allow_unsat_conditions: bool
}

pub struct ExplainedCongr {
    pub expl:     String,
    pub egraph:   LeanEGraph,
    pub report:   Report,
    pub rw_stats: String   
}

pub fn explain_congr(init: String, goal: String, rw_templates: Vec<RewriteTemplate>, facts: Vec<(String, String)>, guides: Vec<String>, cfg: Config, viz_path: Option<String>, e: *const c_void) -> Result<ExplainedCongr, Error> {    
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

    for (name, expr) in facts {
        let expr = expr.parse().map_err(|e : RecExprParseError<_>| Error::Fact(e.to_string()))?;
        let class = egraph.add_expr(&expr);
        egraph[class].data.fact = Some(name.to_string());
    }

    let mut rws;
    match templates_to_rewrites(rw_templates, cfg.block_invalid_matches, cfg.shift_captured_bvars, cfg.allow_unsat_conditions, e) {
        Ok(r)    => rws = r,
        Err(err) => return Err(Error::Rewrite(err.to_string()))
    }
    if cfg.nat_lit    { rws.append(&mut nat_lit_rws(cfg.shapes)) }
    if cfg.eta        { rws.push(eta_reduction_rw()) }
    if cfg.eta_expand { rws.push(eta_expansion_rw()) }
    if cfg.beta       { rws.push(beta_reduction_rw()) }
    if cfg.levels     { rws.append(&mut level_rws()) }
    // TODO: Only add these rws if one of the following is active: beta, eta, eta-expansion, 
    //       bvar index correction. Anything else?
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
    let rw_stats = collect_rw_stats(&runner);

    if runner.egraph.find(init_id) == runner.egraph.find(goal_id) {
        let mut expl = runner.explain_equivalence(&init_expr, &goal_expr);
        let expl_str = expl.get_flat_string();
        Ok(ExplainedCongr { expl: expl_str, egraph: runner.egraph, report, rw_stats })
    } else {
        Ok(ExplainedCongr { expl: "".to_string(), egraph: runner.egraph, report, rw_stats })
    }
}

fn collect_rw_stats(runner: &Runner<LeanExpr, LeanAnalysis>) -> String {
    let mut stats: HashMap<String, usize> = Default::default();
    let mut longest_rw: usize = 0;

    for iter in &runner.iterations {
        for (rw, count) in &iter.applied {
            let rw_str    = rw.to_string();
            let normal_rw = rw_str.strip_suffix("-rev").unwrap_or(&rw_str);
            longest_rw = longest_rw.max(normal_rw.chars().count());

            let current   = stats.get(normal_rw).unwrap_or(&0);
            stats.insert(normal_rw.to_string(), current + count);
        }
    }
    
    let mut entries: Vec<_> = stats.iter().collect();
    entries.sort_by(|l, r| l.0.cmp(r.0));
    
    entries.iter().map(|e| {
        let padding = 1 + longest_rw - e.0.chars().count();
        format!("{}:{}{}", e.0, " ".repeat(padding), e.1)
    })
    .collect::<Vec<_>>()
    .join("\n")
}
