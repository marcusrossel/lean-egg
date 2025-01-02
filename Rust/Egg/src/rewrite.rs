use std::collections::HashMap;
use egg::*;
use std::ffi::c_void;
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

pub fn templates_to_rewrites(
    templates: Vec<RewriteTemplate>, 
    block_invalid_matches: bool, 
    shift_captured_bvars: bool, 
    allow_unsat_conditions: bool,
    e: *const c_void
) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let applier = LeanApplier { 
            rhs: template.rhs, conds: template.conds, 
            block_invalid_matches, shift_captured_bvars, allow_unsat_conditions, e,
        };
        match Rewrite::new(template.name, template.lhs, applier) {
            Ok(rw)   => result.push(rw),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    Ok(result)
}

unsafe impl Send for LeanApplier {}
unsafe impl Sync for LeanApplier {}

struct LeanApplier {
    pub rhs: Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>,
    pub block_invalid_matches: bool,
    pub shift_captured_bvars: bool,
    pub allow_unsat_conditions: bool,
    pub e: *const c_void,
}

impl Applier<LeanExpr, LeanAnalysis> for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, lhs: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // Disallows rewriting on primitive e-nodes.
        if graph[lhs].data.is_primitive { return vec![] }
        
        let searcher_ast = searcher_ast.unwrap();
        let mut var_depths: Option<HashMap<Var, u64>> = None;

        if self.block_invalid_matches || self.shift_captured_bvars { 
            match match_is_valid(subst, searcher_ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        let mut rule = rule;
        for cond in self.conds.clone() {
            let id = graph.add_instantiation(&cond.ast, subst);
            
            if let Some(fact_name) = &graph[id].data.fact {
                let mut r = rule.as_str().to_string(); r.push_str(&fact_name);
                rule = Symbol::from(r);
            } else if eval_eq_condition(&cond, graph, subst) {
                let mut r = rule.as_str().to_string(); r.push_str("!=");
                rule = Symbol::from(r);
            } else if eval_tc_condition(&cond, graph, subst, self.e) {
                let mut r = rule.as_str().to_string(); r.push_str("!%");
                rule = Symbol::from(r);
            } else if self.allow_unsat_conditions {
                let mut r = rule.as_str().to_string(); r.push_str("!?");
                rule = Symbol::from(r);
            } else {
                return vec![]
            }
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing loose bvars.
        // This is the case exactly when `var_depths` is empty.
        if self.shift_captured_bvars && !var_depths.clone().unwrap().is_empty() {
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
