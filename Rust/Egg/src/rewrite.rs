use std::collections::HashMap;
use egg::*;
use std::ffi::c_void;
use crate::basic::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::string_to_c_str;
use crate::valid_match::*;
use crate::is_synthable;

pub struct RewriteConfig {
    block_invalid_matches: bool, 
    shift_captured_bvars: bool, 
    allow_unsat_conditions: bool,
    env: *const c_void
}

impl Config {

    pub fn to_rw_config(&self, env: *const c_void) -> RewriteConfig {
        RewriteConfig {
            block_invalid_matches: self.block_invalid_matches,
            shift_captured_bvars: self.shift_captured_bvars,
            allow_unsat_conditions: self.allow_unsat_conditions,
            env
        }
    }
}

pub struct RewriteTemplate {
    pub name:       String,
    pub lhs:        Pattern<LeanExpr>,
    pub rhs:        Pattern<LeanExpr>,
    pub prop_conds: Vec<Pattern<LeanExpr>>,
    pub tc_conds:   Vec<Pattern<LeanExpr>>,
}

impl RewriteTemplate {

    pub fn to_rewrite(self, cfg: RewriteConfig) -> Res<LeanRewrite> {
        // TODO: How do we handle `allow_unsat_conditions`? One option would be to simply not add
        //       the conditional statements when the option is enabled. I'm not sure what to do 
        //       about tc conditions though, because some of them are a result of tc inst erasure 
        //       and should always be enforced. Perhaps, can we determine which tc conditions are a
        //       result of tc inst erasure and still check those?

        let lhs = if self.prop_conds.is_empty() {
            self.lhs.clone()
        } else {
            let mut str = format!("(= {} {})", self.lhs, self.lhs);

            for cond in self.prop_conds { 
                str = format!("(app (app (const \"And\") {}) {})", str, cond);
            }

            str = format!("(fact {})", str);
            str.parse().expect("Failed to parse lhs in 'RewriteTemplate.to_rewrite'.")
        };

        let applier = LeanApplier { lhs: self.lhs, rhs: self.rhs, tc_conds: self.tc_conds, cfg };
        match Rewrite::new(self.name, lhs, applier) {
            Ok(rw)   => Ok(rw),
            Err(err) => Err(Error::Rewrite(err.to_string()))
        }
    } 
}

unsafe impl Send for LeanApplier {}
unsafe impl Sync for LeanApplier {}

struct LeanApplier {
    pub lhs:      Pattern<LeanExpr>,
    pub rhs:      Pattern<LeanExpr>,
    pub tc_conds: Vec<Pattern<LeanExpr>>,
    pub cfg:      RewriteConfig,
}

impl Applier<LeanExpr, LeanAnalysis> for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        if is_primitive_pattern_subst(&self.lhs, graph, subst) { return vec![] }
        
        let mut var_depths: Option<HashMap<Var, u64>> = None;
        if self.cfg.block_invalid_matches || self.cfg.shift_captured_bvars { 
            match match_is_valid(subst, &self.lhs.ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        for tc_cond in &self.tc_conds {
            if !cond_is_synthable(tc_cond, graph, subst, self.cfg.env) {
                // TODO: Is it correct to simply return the empty vector, or do we need to indicate
                //       which e-cclasses were potentially changed/added by `add_instantiation`?
                return vec![]
            }
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing 
        // loose bvars. This is the case exactly when `var_depths` is empty.
        if self.cfg.shift_captured_bvars && !var_depths.clone().unwrap().is_empty() {
            let shifted_rhs = correct_bvar_indices(&self.rhs, var_depths.unwrap(), graph);
            let (from, did_union) = graph.union_instantiations(&self.lhs.ast, &shifted_rhs, subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = graph.union_instantiations(&self.lhs.ast, &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}

fn cond_is_synthable(cond: &Pattern<LeanExpr>, graph: &mut LeanEGraph, subst: &Subst, env: *const c_void) -> bool {
    let (fresh, i) = in_fresh_graph(cond, graph, subst);
    let ast = fresh.id_to_expr(i);
    let str = string_to_c_str(ast.to_string());
    unsafe { is_synthable(env, str) }
}

// We create a fresh graph, as we don't want to bloat the original e-graph with new stuff,
// but we still want to get access to e-graph analysis of it.
fn in_fresh_graph(cond: &Pattern<LeanExpr>, graph: &LeanEGraph, subst: &Subst) -> (LeanEGraph, Id) {
    let mut fresh = LeanEGraph::new(LeanAnalysis::default()).with_explanations_enabled();

    let mut fresh_subst = Subst::default();
    for pvar in cond.vars() {
        let id = *subst.get(pvar).unwrap();
        let expr = graph.id_to_expr(id);
        let fresh_id = fresh.add_expr(&expr);
        fresh_subst.insert(pvar, fresh_id);
    }

    let i = fresh.add_instantiation(&cond.ast, &fresh_subst);
    (fresh, i)
}

fn is_primitive_pattern_subst(pat: &Pattern<LeanExpr>, graph: &LeanEGraph, subst: &Subst) -> bool {
    match &pat.ast.as_ref().last().unwrap() {
        ENodeOrVar::Var(x) => is_primitive(subst[*x], graph),
        ENodeOrVar::ENode(n) => is_primitive_node(n),
    }
}

pub fn is_primitive_node(node: &LeanExpr) -> bool {
    matches!(node, 
            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Fun(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) | 
            LeanExpr::Succ(_) | LeanExpr::Max(_) | LeanExpr::IMax(_) | LeanExpr::Fact(_) | LeanExpr::Unknown
    )
}

pub fn is_primitive(x: Id, graph: &LeanEGraph) -> bool {
    is_primitive_node(&graph[x].nodes.first().unwrap())
}
