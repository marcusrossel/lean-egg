use std::collections::HashMap;
use egg::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::valid_match::*;
use crate::trace::*;

pub struct RewriteTemplate {
    pub name:  String,
    pub lhs:   Pattern<LeanExpr>,
    pub rhs:   Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>
}

pub fn templates_to_rewrites(templates: Vec<RewriteTemplate>, facts: Vec<RecExpr<LeanExpr>>, block_invalid_matches: bool, shift_captured_bvars: bool) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let applier = LeanApplier { rhs: template.rhs, conds: template.conds, facts: facts.clone(), block_invalid_matches, shift_captured_bvars };
        match Rewrite::new(template.name, template.lhs, applier) {
            Ok(rw)   => result.push(rw),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    Ok(result)
}

struct LeanApplier {
    pub rhs: Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>,
    pub facts: Vec<RecExpr<LeanExpr>>,
    pub block_invalid_matches: bool,
    pub shift_captured_bvars: bool,
}

impl Applier<LeanExpr, LeanAnalysis> for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let searcher_ast = searcher_ast.unwrap();
        let mut var_depths: Option<HashMap<Var, u64>> = None;

        if self.block_invalid_matches || self.shift_captured_bvars { 
            match match_is_valid(subst, searcher_ast, graph) {
                MatchValidity::Invalid   => return vec![],
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        'cond_loop: for cond in self.conds.clone() {
            // `add_instantiation` crashes when the pattern contains variables not covered by the subst.
            // This is currently handled in Lean by filtering out rewrites where a condition's variables are not
            // covered by the body's variables.
            let id = graph.add_instantiation(&cond.ast, subst);
            for fact in self.facts.clone() {
                if id == graph.add_expr(&fact) { continue 'cond_loop }
            } 
            return vec![] // This is only reached if `cond` is not satisfied by any fact.
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing loose bvars.
        // This is the case exactly when `var_depths` is empty.
        if self.shift_captured_bvars && !var_depths.clone().unwrap().is_empty() {
            dbg_trace(format!("Start capture avoidance for\n  LHS: {}\n  RHS: {}\n  RHS Raw: {:?}\n  subst: {:?}", searcher_ast, self.rhs, self.rhs.ast.as_ref(), subst), TraceGroup::BVarCorrection);
            let (shifted_subst, shifted_rhs) = correct_bvar_indices(subst, &self.rhs, var_depths.unwrap(), graph);
            dbg_trace("End capture avoidance\n", TraceGroup::BVarCorrection);
            let (from, did_union) = graph.union_instantiations(searcher_ast, &shifted_rhs, &shifted_subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = graph.union_instantiations(searcher_ast, &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}
