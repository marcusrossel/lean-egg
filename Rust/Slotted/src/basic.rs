use slotted_egraphs::*;
use crate::result::*;
use crate::analysis::*;
use crate::beta::*;
use crate::eta::*;
use crate::levels::*;
use crate::nat_lit::*;
use crate::rewrite::*;

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
    subgoals:        bool
}

pub fn explain_congr(
    init: String, goal: String, rw_templates: Vec<RewriteTemplate>, guides: Vec<String>, 
    cfg: Config, _viz_path: Option<String>
) -> Result<(String, LeanEGraph, Report), Error> {    
    let mut egraph: LeanEGraph = EGraph::new();

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

    let mut rws;
    match templates_to_rewrites(rw_templates, cfg.subgoals) {
        Ok(r)    => rws = r,
        Err(err) => return Err(Error::Rewrite(err.to_string()))
    }
    if cfg.nat_lit    { rws.append(&mut nat_lit_rws()) }
    if cfg.eta        { rws.push(eta_reduction_rw()) }
    if cfg.eta_expand { rws.push(eta_expansion_rw()) }
    if cfg.beta       { rws.append(&mut beta_reduction_rws(/*small_step:*/false)) }
    if cfg.levels     { rws.append(&mut level_rws()) }

    let i = init_id.clone();
    let g = goal_id.clone();
    let report = run_eqsat(&mut egraph, rws, cfg.iter_limit, cfg.time_limit, move |egraph| {
        if egraph.eq(&i, &g) {
            Err("proved goal".to_string())
        } else {
            Ok(())
        }
    });

    if egraph.eq(&init_id, &goal_id) {
        let expl = egraph.explain_equivalence(init_expr, goal_expr);

        // HACK: For debugging purposes we're abusing the `optimize_expl` option to indicate whether 
        //       the tree explanation should be returned instead of a flat explanation. A value of 
        //       `false` indicates that the tree explanation should be returned.
        if !cfg.optimize_expl {
            let tree_expl = expl.to_string(&egraph);
            Ok((tree_expl, egraph, report))
        } else {
            let flat_expl = expl.to_flat_string(&egraph);
            Ok((flat_expl, egraph, report))
        }
    } else {
        Ok(("".to_string(), egraph, report))
    }
}