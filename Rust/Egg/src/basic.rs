use std::time::Duration;
use std::collections::HashMap;
use std::ffi::c_void;
use egg::*;
use crate::activation::*;
use crate::analysis::*;
use crate::beta::*;
use crate::eta::*;
use crate::expl::*;
use crate::lean_expr::*;
use crate::levels::*;
use crate::nat_lit::*;
use crate::result::*;
use crate::rewrite::*;
use crate::shift::*;
use crate::subst::*;
use crate::util::*;

#[repr(C)]
pub struct Config {
    optimize_expl:   bool,
    time_limit:      usize,
    node_limit:      usize,
    iter_limit:      usize, 
    nat_lit:         bool, 
    eta:             bool,
    eta_expand:      bool,
    beta:            bool,
    levels:          bool,
    shapes:          bool,
    union_semantics: bool,
    pub subgoals:    bool
}

pub struct ExplainedCongr {
    pub kind:        ExplanationKind,
    pub expl:        String,
    pub egraph:      LeanEGraph,
    pub report:      Report,
    pub rw_stats:    String,
    pub activations: Activations   
}

pub fn explain_congr(
    init: String, goal: String, rw_templates: Vec<RewriteTemplate>, 
    guides: Vec<String>, cfg: Config, viz_path: Option<String>, env: *const c_void
) -> Result<ExplainedCongr, Error> {    
    let init = mk_initial_egraph(init, goal, guides, &cfg)?;
    let activations = get_activations(&init, &rw_templates);
    let Initialized { mut egraph, init_id, init_expr, goal_id, goal_expr, guide_exprs: _ } = init;
    let (eqs, rws) = mk_rewrites(rw_templates, &cfg, &activations, env)?;

    // Adds ground equalities to the e-graph.
    for eq in eqs { 
        egraph.union_instantiations(&eq.lhs, &eq.rhs, &Subst::with_capacity(0), eq.name); 
    }

    let mut runner = mk_runner(egraph, init_id, goal_id, &cfg, viz_path).run(&rws);
    let report = runner.report();
    let rw_stats = collect_rw_stats(&runner);
    let (kind, expl) = mk_explanation(&mut runner.egraph, init_expr, goal_expr, init_id, goal_id);
    Ok(ExplainedCongr { kind, expl, egraph: runner.egraph, report, rw_stats, activations })
}

struct Initialized {
    egraph: LeanEGraph,
    init_id: Id,
    init_expr: RecExpr<LeanExpr>,
    goal_id: Id,
    goal_expr: RecExpr<LeanExpr>,
    guide_exprs: Vec<RecExpr<LeanExpr>>
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
    let mut guide_exprs = vec![];
    for guide in guides {
        let expr = guide.parse().map_err(|e : RecExprParseError<_>| Error::Guide(e.to_string()))?;
        egraph.add_expr(&expr);
        guide_exprs.push(expr);
    }

    // Adds `True` as a fact to the e-graph.
    let true_expr = "(const \"True\")".parse().unwrap();
    let true_fact = format!("(fact {})", true_expr).parse().unwrap();
    egraph.add_expr(&true_fact); 

    // Marks `p ∧ q` as a fact for any given facts `p` and `q`.
    // NOTE: We could also add this as a regular theorem sent from Lean.
    let and_true_expr = "(app (app (const \"And\") (const \"True\")) (const \"True\"))".parse().unwrap();
    egraph.union_instantiations(&true_expr, &and_true_expr, &Subst::with_capacity(0), "∧");

    Ok(Initialized { egraph, init_id, init_expr, goal_id, goal_expr, guide_exprs })
}

fn get_activations(init: &Initialized, rw_templates: &Vec<RewriteTemplate>) -> Activations {
    let mut exprs: Vec<PatternAst<LeanExpr>> = vec![];
    exprs.push(init.init_expr.clone().into_iter().map(ENodeOrVar::ENode).collect());
    exprs.push(init.goal_expr.clone().into_iter().map(ENodeOrVar::ENode).collect());
    for guide in &init.guide_exprs { 
        exprs.push(guide.clone().into_iter().map(ENodeOrVar::ENode).collect()) 
    }
    for template in rw_templates { 
        exprs.push(template.lhs.ast.clone()); 
        exprs.push(template.rhs.ast.clone()); 
        for prop_cond in &template.prop_conds { exprs.push(prop_cond.ast.clone()) }
    }
    let mut activations: Activations = Default::default();
    for expr in exprs { activations.merge(&Activations::of(&expr)) }
    activations
}
 
fn mk_rewrites(
    rw_templates: Vec<RewriteTemplate>, cfg: &Config, is_active: &Activations, env: *const c_void
) -> Result<(Vec<GroundEq>, Vec<LeanRewrite>), Error> {
    let mut eqs = vec![];
    let mut rws = vec![
        rewrite!("EQ"; "(app (app (app (const \"Eq\" ?u) ?t) ?l) ?r)" => "(= ?l ?r)")
    ];

    for template in rw_templates { 
        // When `is_active.binders() == false`, the rewrite config does not enable checking of 
        // invalid matches and bvar index correction.
        match template.to_rewrite(cfg.to_rw_config(is_active.binders(), env))? {
            Either::Left(rw)  => rws.push(rw),
            Either::Right(eq) => eqs.push(eq)
        }
    }

    if is_active.lambda {
        if cfg.eta        { rws.push(eta_reduction_rw()) }
        if cfg.eta_expand { rws.push(eta_expansion_rw()) }
        if cfg.beta       { 
            rws.push(beta_reduction_rw());
            // We only enable substitution rewrites if beta-reduction is active, because 
            // beta-reduction is the only source of substitution nodes. 
            rws.append(&mut subst_rws())
        }
    }

    // When no binders are present, we don't need to include rewrite rules for shift nodes as these
    // nodes only originate from beta- and eta-reduction or bvar index correction -- which are all
    // disabled when no binders are present.
    if is_active.binders() { rws.append(&mut shift_rws()) }

    if is_active.nat_lit && cfg.nat_lit { rws.append(&mut nat_lit_rws(cfg.shapes)) }
    if is_active.level && cfg.levels    { rws.append(&mut level_rws()) }
    
    Ok((eqs, rws))
}

fn mk_runner(
    egraph: LeanEGraph, init_id: Id, goal_id: Id, cfg: &Config, viz_path: Option<String>
) -> Runner<LeanExpr, LeanAnalysis> {
    let true_expr = "(const \"True\")".parse().unwrap();
    let true_id = egraph.lookup_expr(&"(const \"True\")".parse().unwrap()).unwrap();
    
    let mut runner = Runner::default()
        .with_egraph(egraph)
        .with_time_limit(Duration::from_secs(cfg.time_limit.try_into().unwrap()))
        .with_node_limit(cfg.node_limit)
        .with_iter_limit(cfg.iter_limit)
        .with_hook(move |runner| {
            // Note: `lookup` returns a canonicalized id.
            if runner.egraph.lookup(LeanExpr::Eq([init_id, goal_id])) == Some(runner.egraph.find(true_id)) {
                Err("Proved goal!".to_string())
            } else {
                Ok(())
            }   
        })
        .with_hook(move |runner| {
            for class in runner.egraph.classes().map(|x| x.id).collect::<Vec<_>>() {
                if is_primitive(class, &runner.egraph) { continue }
                let (_, rep) = Extractor::new(&runner.egraph, AstSize).find_best(class);
                let eq_expr = format!("(= {} {})", rep, rep).parse().unwrap();
                runner.egraph.union_instantiations(&eq_expr, &true_expr, &Subst::with_capacity(0), "=");
            }
            runner.egraph.rebuild();
            Ok(())
        });

    if let Some(path) = viz_path {
        runner = runner.with_hook(move |runner| {
            runner.egraph.dot().to_dot(format!("{}/{}.dot", path, runner.iterations.len())).unwrap();
            Ok(())
        })
    }

    runner
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
