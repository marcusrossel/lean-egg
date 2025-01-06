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
    optimize_expl:              bool,
    time_limit:                 usize,
    node_limit:                 usize,
    iter_limit:                 usize, 
    nat_lit:                    bool, 
    eta:                        bool,
    eta_expand:                 bool,
    beta:                       bool,
    levels:                     bool,
    shapes:                     bool,
    pub block_invalid_matches:  bool,
    pub shift_captured_bvars:   bool,
    union_semantics:            bool,
    pub allow_unsat_conditions: bool
}

pub struct ExplainedCongr {
    pub expl:     String,
    pub egraph:   LeanEGraph,
    pub report:   Report,
    pub rw_stats: String   
}

pub fn explain_congr(
    init: String, goal: String, rw_templates: Vec<RewriteTemplate>, 
    guides: Vec<String>, cfg: Config, viz_path: Option<String>, env: *const c_void
) -> Result<ExplainedCongr, Error> {    
    // TODO: For rewrites which don't contain conditions or pattern vars: only run the rewrite once
    //       before eqsat by adding the LHS and RHS to the e-graph and unioning them.
    
    let Initialized { egraph, init_id, init_expr, goal_id, goal_expr } = 
        mk_initial_egraph(init, goal, guides, &cfg)?;

    let rws = mk_rewrites(rw_templates, &cfg, env)?;

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
        .with_hook(move |runner| {
            let eg = &mut runner.egraph;
            let true_expr = "(const \"True\")".parse().unwrap();
            let true_class = eg.add_expr(&true_expr);
            let ids: Vec<_> = eg.classes().map(|x| x.id).collect();
            for x in ids {
                if !eg[x].data.is_primitive {
                    let a = eg.add(LeanExpr::Eq([x, x]));
                    eg.union_trusted(a, true_class, "=");
                }
            }
            eg.rebuild();
            Ok(())
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

struct Initialized {
    egraph: LeanEGraph,
    init_id: Id,
    init_expr: RecExpr<LeanExpr>,
    goal_id: Id,
    goal_expr: RecExpr<LeanExpr>
}

fn mk_initial_egraph(
    init: String, goal: String, guides: Vec<String>, cfg: &Config
) -> Result<Initialized, Error> {
    let analysis = LeanAnalysis { union_semantics: cfg.union_semantics };
    let mut egraph: LeanEGraph = EGraph::new(analysis);

    // Enables explanations.
    egraph = egraph.with_explanations_enabled();
    if !cfg.optimize_expl { egraph = egraph.without_explanation_length_optimization() }

    // Adds the LHS and RHS of the goal we're trying to prove to the e-graph.
    let init_expr = init.parse().map_err(|e : RecExprParseError<_>| Error::Init(e.to_string()))?;
    let goal_expr = goal.parse().map_err(|e : RecExprParseError<_>| Error::Goal(e.to_string()))?;
    let init_id = egraph.add_expr(&init_expr);
    let goal_id = egraph.add_expr(&goal_expr);

    // Adds the guide terms to the e-graph.
    for guide in guides {
        let expr = guide.parse().map_err(|e : RecExprParseError<_>| Error::Guide(e.to_string()))?;
        egraph.add_expr(&expr);
    }

    // Adds `True` to the e-graph.
    let true_expr = "(const \"True\")".parse().unwrap();
    let true_id = egraph.add_expr(&true_expr);

    // Marks `True` as a fact.
    let true_fact = format!("(fact {})", true_expr).parse().unwrap();
    egraph.add_expr(&true_fact); 

    // Marks `p ∧ q` as a fact for any given facts `p` and `q`.
    let and_true = "(app (app (const \"And\") (const \"True\")) (const \"True\"))".parse().unwrap();
    let and_id = egraph.add_expr(&and_true); 
    egraph.union_trusted(true_id, and_id, "AND_FACT");

    Ok(Initialized { egraph, init_id, init_expr, goal_id, goal_expr })
}
 
fn mk_rewrites(rw_templates: Vec<RewriteTemplate>, cfg: &Config, env: *const c_void) -> Result<Vec<LeanRewrite>, Error> {
    let mut rws = vec![
        rewrite!("EQ"; "(app (app (app (const \"Eq\" ?u) ?t) ?l) ?r)" => "(= ?l ?r)")
    ];

    for template in rw_templates { rws.push(template.to_rewrite(cfg.to_rw_config(env))?) }
    if cfg.nat_lit               { rws.append(&mut nat_lit_rws(cfg.shapes)) }
    if cfg.eta                   { rws.push(eta_reduction_rw()) }
    if cfg.eta_expand            { rws.push(eta_expansion_rw()) }
    if cfg.beta                  { rws.push(beta_reduction_rw()) }
    if cfg.levels                { rws.append(&mut level_rws()) }
    // TODO: Only add these rws if one of the following is active: beta, eta, eta-expansion, 
    //       bvar index correction. Anything else?
    rws.append(&mut subst_rws());
    rws.append(&mut shift_rws());
    
    Ok(rws)
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
