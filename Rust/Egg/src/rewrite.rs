use std::collections::HashMap;
use egg::*;
use std::ffi::c_void;
use crate::basic::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::valid_match::*;
use crate::is_synthable;

pub struct RewriteTemplate {
    pub name:  String,
    pub lhs:   Pattern<LeanExpr>,
    pub rhs:   Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>
}

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

impl RewriteTemplate {

    pub fn to_rewrite(self, cfg: RewriteConfig) -> Res<LeanRewrite> {
        let applier = LeanApplier { rhs: self.rhs, conds: self.conds, cfg };
        match Rewrite::new(self.name, self.lhs, applier) {
            Ok(rw)   => Ok(rw),
            Err(err) => Err(Error::Rewrite(err.to_string()))
        }
    } 
}

unsafe impl Send for LeanApplier {}
unsafe impl Sync for LeanApplier {}

struct LeanApplier {
    pub rhs: Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>,
    pub cfg: RewriteConfig,
}

impl Applier<LeanExpr, LeanAnalysis> for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, lhs: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // Disallows rewriting on primitive e-nodes.
        if graph[lhs].data.is_primitive { return vec![] }
        
        let searcher_ast = searcher_ast.unwrap();
        let mut var_depths: Option<HashMap<Var, u64>> = None;

        if self.cfg.block_invalid_matches || self.cfg.shift_captured_bvars { 
            match match_is_valid(subst, searcher_ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        // Checks for satisfaction of rewrite conditions, and aborts if any is not satisfied.
        let mut rule = rule;
        for cond in self.conds.clone() {
            if let Some(fact) = fact_for_cond(cond, graph, subst) {
                let mut r = rule.as_str().to_string(); r.push_str(&fact);
                rule = Symbol::from(r);
            } else if self.cfg.allow_unsat_conditions {
                let mut r = rule.as_str().to_string(); r.push_str("!?");
                rule = Symbol::from(r);
            } else {
                // TODO: Is it correct to return the empty vec here? We did potentially change
                //       the egraph by adding conditions' instantiations.
                return vec![]
            }
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing 
        // loose bvars. This is the case exactly when `var_depths` is empty.
        if self.cfg.shift_captured_bvars && !var_depths.clone().unwrap().is_empty() {
            let shifted_rhs = correct_bvar_indices(&self.rhs, var_depths.unwrap(), graph);
            let (from, did_union) = graph.union_instantiations(searcher_ast, &shifted_rhs, subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = graph.union_instantiations(searcher_ast, &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}

fn fact_for_cond(cond: Pattern<LeanExpr>, graph: &mut LeanEGraph, subst: &Subst) -> Option<String> {
    let id = graph.add_instantiation(&cond.ast, subst);
    let ast = graph.id_to_expr(id);
    let head = Id::from(ast.as_ref().len() - 1);
    
    match &ast[head] {
        LeanExpr::Proof(prop) => {
            // TODO: We can't determine how this fact was proven, can we?
            if graph.lookup(LeanExpr::Fact(*prop)).is_some() {
                Some("!∀".to_string())
            } else if true {
                // TODO: Since we don't *completely* reify equalities (we erase the type and 
                // universe) we still need special handling for equality conditions.
                todo!()
            } else {
                // TODO: Is it correct to return the empty vec here? We did potentially change
                //       the egraph by adding the condition's instantiation.
                None
            }
        },
        LeanExpr::Inst(class) => {
            todo!()
        },
        _ => None
    }
}

fn eval_eq_condition(cond: &Pattern<LeanExpr>, graph: &mut LeanEGraph, subst: &Subst) -> bool {
    // check whether `cond` is an equality condition.
    // "(app (app (app (const 'Eq' ?univ...) ?t) ?a) ?b)"
    //  ^i1  ^i2  ^i3  ^i4    ^i5  ^i6       ^i7 ^i8 ^i9
    let i = graph.add_instantiation(&cond.ast, subst);
    let ast = graph.id_to_expr(i);

    let i1 = Id::from(ast.as_ref().len() - 1);
    let LeanExpr::App([i2, i9])  = &ast[i1]  else { return false };
    let LeanExpr::App([i3, i8_]) = &ast[*i2] else { return false };
    let LeanExpr::App([i4, _i7]) = &ast[*i3] else { return false };
    let LeanExpr::Const(b)       = &ast[*i4] else { return false };
    let [i5, ..]                 = &**b      else { return false };
    let LeanExpr::Str(string)    = &ast[*i5] else { return false };
    let "Eq"                     = &**string else { return false };

    let (a, b) = (sub_expr(&ast, *i8_), sub_expr(&ast, *i9));
    graph.lookup_expr(&a) == graph.lookup_expr(&b)
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

fn sub_expr(ast: &RecExpr<LeanExpr>, i: Id) -> RecExpr<LeanExpr> {
    let v: Vec<_> = ast.as_ref()[0..=usize::from(i)].iter().cloned().collect();
    RecExpr::from(v)
}
