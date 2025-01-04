use std::collections::HashMap;
use egg::*;
use std::ffi::c_void;
use crate::basic::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::util::sub_expr;
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
        let lhs_id = graph.add_instantiation(&self.lhs.ast, subst);
        
        // Disallows rewriting on primitive e-nodes.
        if graph[lhs_id].data.is_primitive { return vec![] }
        
        let mut var_depths: Option<HashMap<Var, u64>> = None;
        if self.cfg.block_invalid_matches || self.cfg.shift_captured_bvars { 
            match match_is_valid(subst, &self.lhs.ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        // TODO: Check tc conditions.

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

fn eval_tc_condition(cond: &Pattern<LeanExpr>, graph: &mut LeanEGraph, subst: &Subst, e: *const c_void) -> bool {
    let i = graph.add_instantiation(&cond.ast, subst);
    let ast = graph.id_to_expr(i);

    let i1 = Id::from(ast.as_ref().len() - 1);
    let LeanExpr::Inst(ty_id) = &ast[i1] else { return false };
    let ty = sub_expr(&ast, *ty_id);

    let mut s = ty.to_string();
    s.push('\0');
    unsafe { is_synthable(e, s.as_ptr()) }
}
