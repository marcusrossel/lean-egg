use std::cell::RefCell;
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
use crate::util::*;

pub struct RewriteConfig {
    binders_are_active: bool,
    subgoals: bool,
    env: *const c_void
}

impl Config {

    pub fn to_rw_config(&self, binders_are_active: bool, env: *const c_void) -> RewriteConfig {
        RewriteConfig {
            binders_are_active,
            subgoals: self.subgoals,
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
    pub weak_vars:  Vec<Var>,
    pub blocks:     Vec<RecExpr<LeanExpr>>
}

pub struct GroundEq {
    pub name: String,
    pub lhs : PatternAst<LeanExpr>,
    pub rhs : PatternAst<LeanExpr>
}

impl RewriteTemplate {

    pub fn to_rewrite(self, cfg: RewriteConfig) -> Res<Either<LeanRewrite, GroundEq>> {
        // If the rewrite contains neither conditions nor pattern variables, it's a ground equation.
        if self.prop_conds.is_empty() && self.tc_conds.is_empty() && 
           self.lhs.vars().is_empty() && self.rhs.vars().is_empty() {
            return Ok(Either::Right(GroundEq { name: self.name, lhs: self.lhs.ast, rhs: self.rhs.ast }))
        }

        let lhs = if self.prop_conds.is_empty() || cfg.subgoals {
            self.lhs.clone()
        } else {
            let mut str = format!("(= {} {})", self.lhs, self.lhs);

            for cond in self.prop_conds.iter() { 
                str = format!("(app (app (const \"And\") {}) {})", str, cond);
            }

            str = format!("(fact {})", str);
            str.parse().expect("Failed to parse lhs in 'RewriteTemplate.to_rewrite'.")
        };

        let applier = LeanApplier { 
            lhs: self.lhs, rhs: self.rhs, tc_conds: self.tc_conds, prop_conds: self.prop_conds, 
            weak_vars: self.weak_vars, blocks: self.blocks, cfg 
        };
        match Rewrite::new(self.name, lhs, applier) {
            Ok(rw)   => Ok(Either::Left(rw)),
            Err(err) => Err(Error::Rewrite(err.to_string()))
        }
    } 
}

unsafe impl Send for LeanApplier {}
unsafe impl Sync for LeanApplier {}

struct LeanApplier {
    pub lhs:        Pattern<LeanExpr>,
    pub rhs:        Pattern<LeanExpr>,
    pub tc_conds:   Vec<Pattern<LeanExpr>>,
    pub prop_conds: Vec<Pattern<LeanExpr>>,
    pub weak_vars:  Vec<Var>,
    pub blocks:     Vec<RecExpr<LeanExpr>>, // TODO: This could be extended to cover patterns, if needed.
    pub cfg:        RewriteConfig,
}

impl Applier<LeanExpr, LeanAnalysis> for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        if is_primitive_pattern_subst(&self.lhs, graph, subst) { return vec![] }
        
        let mut var_depths: Option<HashMap<Var, u64>> = None;
        if self.cfg.binders_are_active { 
            match match_is_valid(subst, &self.lhs.ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        for tc_cond in &self.tc_conds {
            if !cond_is_synthable(tc_cond, graph, subst, self.cfg.env) {
                return vec![]
            }
        }

        let mut rule = rule;
        if self.cfg.subgoals {
            if !self.blocks.is_empty() {
                // If subgoals are activated, still check that no conditional proposition is blocked.
                for prop_cond in self.prop_conds.iter() {
                    let (fresh, i) = in_fresh_graph(prop_cond, graph, subst);
                    let prop_cond_expr = fresh.id_to_expr(i);  
                    if self.blocks.contains(&prop_cond_expr) {
                        return vec![]
                    }
                }       
            }   
        } else if !self.weak_vars.is_empty() {
            // If subgoals are not activated, assign weak vars (if any exists).
            let mut r = rule.as_str().to_string();
            for var in &self.weak_vars {
                let assignment = format!("{}={:?}", var.to_string().replace("?", ","), subst[*var]);
                r.push_str(&assignment);
            }
            rule = Symbol::from(r);
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing 
        // loose bvars. This is the case exactly when `var_depths` is empty.
        if self.cfg.binders_are_active && !var_depths.clone().unwrap().is_empty() {
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

thread_local! {
    static TC_CACHE: RefCell<HashMap<RecExpr<LeanExpr>, bool>> = RefCell::new(Default::default());
}

fn cond_is_synthable(cond: &Pattern<LeanExpr>, graph: &mut LeanEGraph, subst: &Subst, env: *const c_void) -> bool {
    let (fresh, i) = in_fresh_graph(cond, graph, subst);
    let ast = fresh.id_to_expr(i);
    TC_CACHE.with_borrow_mut(|cache|
        if let Some(result) = cache.get(&ast) {
            *result 
        } else {            
            let str = string_to_c_str(ast.to_string());
            let result = unsafe { is_synthable(env, str) };
            cache.insert(ast, result);
            result
        }
    )
}

// We create a fresh graph, as we don't want to bloat the original e-graph with new stuff,
// but we still want to get access to e-graph analysis of it.
fn in_fresh_graph(cond: &Pattern<LeanExpr>, graph: &LeanEGraph, subst: &Subst) -> (LeanEGraph, Id) {
    let mut fresh = LeanEGraph::new(LeanAnalysis::default()).with_explanations_enabled();

    let mut fresh_subst = Subst::default();
    for pvar in cond.vars() {
        let expr = graph.id_to_expr(subst[pvar]);
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
