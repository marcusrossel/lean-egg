use std::cell::Cell;
use std::ffi::c_void;
use std::rc::Rc;
use std::time::{Duration, Instant};
use rs2::*;
use crate::activation::*;
use crate::analysis::*;
use crate::beta::*;
use crate::egraph::*;
use crate::eta::*;
use crate::expl::*;
use crate::lean_expr::*;
use crate::levels::*;
use crate::nat_lit::*;
use crate::proof::*;
use crate::result::*;
use crate::rewrite::*;
use crate::shift::*;
use crate::subst::*;
use crate::util::*;

#[repr(C)]
pub struct Config {
    #[allow(dead_code)] // GUF does not optimize explanations.
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

// Analogous to egg's `Report`.
pub struct Report {
    pub iterations:     usize,
    pub stop_reason:    StopReason,
    pub egraph_nodes:   usize,
    pub egraph_classes: usize,
    pub total_time:     f64,
}

pub struct ExplainedCongr {
    pub kind:        ExplanationKind,
    pub expl:        String,
    pub egraph:      LeanEGraphObj,
    pub report:      Report,
    pub activations: Activations
}

// Note: GUF cannot export e-graphs as dot-files, so `_viz_path` is ignored.
pub fn explain_congr(
    init: String, goal: String, rw_templates: Vec<RewriteTemplate>,
    guides: Vec<String>, cfg: Config, _viz_path: Option<String>, env: *const c_void
) -> Result<ExplainedCongr, Error> {
    LeanAnalysis::set_union_semantics(cfg.union_semantics);
    start_recording_enodes();

    let init = mk_initial_egraph(init, goal, guides)?;
    let activations = get_activations(&init, &rw_templates);
    let Initialized { mut egraph, init_id, init_expr, goal_id, goal_expr, guide_exprs: _ } = init;
    let (eqs, rws) = mk_rewrites(rw_templates, &cfg, &activations, env)?;

    // Adds ground equalities to the e-graph.
    for eq in eqs {
        union_terms(&mut egraph, &eq.lhs, &eq.rhs, &eq.name);
    }

    let iterations = Rc::new(Cell::new(0));
    let hooks = mk_hooks(&egraph, init_id.clone(), goal_id.clone(), iterations.clone());
    let time_limit = Duration::from_secs(cfg.time_limit.try_into().unwrap());
    let start_time = Instant::now();
    let stop_reason = eqsat(&mut egraph, &rws, hooks, time_limit, cfg.node_limit, cfg.iter_limit);
    let total_time = start_time.elapsed();
    // Equality saturation may stop before rebuilding the e-graph.
    egraph.rebuild();

    let report = Report {
        iterations:     iterations.get(),
        stop_reason,
        egraph_nodes:   egraph.hashcons.len(),
        egraph_classes: egraph.classes().len(),
        total_time:     total_time.as_secs_f64()
    };
    let egraph = LeanEGraphObj { egraph, enodes: finish_recording_enodes() };
    let (kind, expl) = mk_explanation(&egraph.egraph, init_expr, goal_expr, init_id, goal_id);
    Ok(ExplainedCongr { kind, expl, egraph, report, activations })
}

struct Initialized {
    egraph: LeanEGraph,
    init_id: PId,
    init_expr: LeanTerm,
    goal_id: PId,
    goal_expr: LeanTerm,
    guide_exprs: Vec<LeanTerm>
}

fn mk_initial_egraph(init: String, goal: String, guides: Vec<String>) -> Result<Initialized, Error> {
    // Note: Unlike egg, GUF always tracks proofs, so we don't need to enable explanations.
    let mut egraph: LeanEGraph = EGraph::new();

    // Adds the LHS and RHS of the goal we're trying to prove to the e-graph.
    let init_expr = parse_term(&init).map_err(Error::Init)?;
    let goal_expr = parse_term(&goal).map_err(Error::Goal)?;
    let init_id = add_expr(&init_expr, &mut egraph);
    let goal_id = add_expr(&goal_expr, &mut egraph);

    // Adds the guide terms to the e-graph.
    let mut guide_exprs = vec![];
    for guide in guides {
        let expr = parse_term(&guide).map_err(Error::Guide)?;
        add_expr(&expr, &mut egraph);
        guide_exprs.push(expr);
    }

    // Adds `True` as a fact to the e-graph.
    let true_expr = term("(const \"True\")");
    let true_fact = term(&format!("(fact {:?})", true_expr));
    add_expr(&true_fact, &mut egraph);

    // Marks `p ∧ q` as a fact for any given facts `p` and `q`.
    // NOTE: We could also add this as a regular theorem sent from Lean.
    let and_true_expr = term("(app (app (const \"And\") (const \"True\")) (const \"True\"))");
    union_terms(&mut egraph, &true_expr, &and_true_expr, "∧");

    Ok(Initialized { egraph, init_id, init_expr, goal_id, goal_expr, guide_exprs })
}

fn get_activations(init: &Initialized, rw_templates: &Vec<RewriteTemplate>) -> Activations {
    let mut exprs: Vec<&LeanPattern> = vec![];
    exprs.push(&init.init_expr);
    exprs.push(&init.goal_expr);
    for guide in &init.guide_exprs {
        exprs.push(guide)
    }
    for template in rw_templates {
        exprs.push(&template.lhs);
        exprs.push(&template.rhs);
        for prop_cond in &template.prop_conds { exprs.push(prop_cond) }
    }
    let mut activations: Activations = Default::default();
    for expr in exprs { activations.merge(&Activations::of(expr)) }
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
            Either::L(rw) => rws.push(rw),
            Either::R(eq) => eqs.push(eq)
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

fn mk_hooks(egraph: &LeanEGraph, init_id: PId, goal_id: PId, iterations: Rc<Cell<usize>>) -> Box<[Hook<LeanAnalysis>]> {
    let true_id = egraph.lookup_term(&term("(const \"True\")")).unwrap();
    let goal_true_id = true_id.clone();

    let hooks: Vec<Hook<LeanAnalysis>> = vec![
        // GUF's `eqsat` does not report the number of iterations, so we count them here.
        Box::new(move |_: &mut LeanEGraph| {
            iterations.set(iterations.get() + 1);
            Ok(())
        }),
        Box::new(move |egraph: &mut LeanEGraph| {
            // Note: `lookup` canonicalizes the children of the given e-node.
            let goal_eq = LeanExpr::Eq([init_id.clone(), goal_id.clone()]);
            if egraph.lookup(&goal_eq).map(|x| egraph.find(x).1) == Some(egraph.find(goal_true_id.clone()).1) {
                Err(StopReason::Other("Proved goal!".to_string()))
            } else {
                Ok(())
            }
        }),
        Box::new(move |egraph: &mut LeanEGraph| {
            // Unlike the egg backend, we don't need to extract a representative term for each
            // e-class, as GUF justifies unions of (proof-annotated) e-classes instead of terms.
            let classes: Box<[Id]> = egraph.classes().iter()
                .copied()
                .filter(|x| !is_primitive(*x, egraph))
                .collect();

            for x in classes {
                let rep = (Proof::identity(), x);
                let eq = egraph.add(&LeanExpr::Eq([rep.clone(), rep]));
                union_justified(egraph, eq, true_id.clone(), "=");
            }
            egraph.rebuild();
            Ok(())
        }),
    ];

    hooks.into_boxed_slice()
}
