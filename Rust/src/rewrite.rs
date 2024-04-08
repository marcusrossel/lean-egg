use egg::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::valid_match::*;
use crate::trace::*;

pub struct RewriteTemplate {
    pub name: String,
    pub lhs: Pattern<LeanExpr>,
    pub rhs: Pattern<LeanExpr>
}

pub fn templates_to_rewrites(templates: Vec<RewriteTemplate>, block_invalid_matches: bool, shift_captured_bvars: bool) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let rw = if shift_captured_bvars || block_invalid_matches { 
            // As this applier is only used when at least one of the given options is true,
            // and `shift_captured_bvars` perform `block_invalid_matches` as a pre-processing 
            // step, we always perform `block_invalid_matches` and thus don't need to pass it 
            // as an option.
            let applier = SafeApplier { rhs: template.rhs, shift_captured_bvars };
            Rewrite::new(template.name, template.lhs, applier)
        } else { 
            Rewrite::new(template.name, template.lhs, template.rhs) 
        };
        match rw {
            Ok(r) => result.push(r),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    Ok(result)
}

struct SafeApplier {
    pub rhs: Pattern<LeanExpr>,
    pub shift_captured_bvars: bool,
}

impl Applier<LeanExpr, LeanAnalysis> for SafeApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let searcher_ast = searcher_ast.unwrap();
        
        match match_is_valid(subst, searcher_ast, graph) {
            MatchValidity::Invalid => vec![],
            MatchValidity::Valid(var_depths) => {
                // A substitution needs no shifting if it does not map any variables to e-classes containing loose bvars.
                // This is the case exactly when `var_depths` is empty.
                if !self.shift_captured_bvars || var_depths.is_empty() {
                    // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
                    let (from, did_union) = graph.union_instantiations(searcher_ast, &self.rhs.ast, subst, rule);
                    if did_union { vec![from] } else { vec![] }
                } else {
                    dbg_trace(format!("Start capture avoidance for\n  LHS: {}\n  RHS: {}\n  RHS Raw: {:?}\n  subst: {:?}", searcher_ast, self.rhs, self.rhs.ast.as_ref(), subst), TraceGroup::BVarCorrection);
                    let (shifted_subst, shifted_rhs) = correct_bvar_indices(subst, &self.rhs, var_depths, graph);
                    dbg_trace("End capture avoidance\n", TraceGroup::BVarCorrection);
                    let (from, did_union) = graph.union_instantiations(searcher_ast, &shifted_rhs, &shifted_subst, rule);
                    if did_union { vec![from] } else { vec![] }
                }
            }
        }
    }
}