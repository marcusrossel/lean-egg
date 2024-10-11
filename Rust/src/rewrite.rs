use std::collections::HashMap;
use slotted_egraphs::*;
use crate::result::*;
use crate::lean_expr::*;

pub struct RewriteTemplate {
    pub name:  String,
    pub lhs:   Pattern<LeanExpr>,
    pub rhs:   Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>
}

pub fn templates_to_rewrites(
    templates: Vec<RewriteTemplate>, 
    facts: HashMap<AppliedId, String>, 
    allow_unsat_conditions: bool
) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let lhs = template.lhs.clone();
        let facts = facts.clone();
        let rw = RewriteT {
            searcher: Box::new(move |graph| { ematch_all(graph, &lhs) }),
            applier: Box::new(move |substs, graph| {
                for subst in substs {
                    // Disallows rewriting on primitive e-nodes.
                    // TODO: if graph[lhs].data.is_primitive { return vec![] }

                    let mut rule = template.name.clone();
                    
                    for cond in template.conds.clone() {

                        let id = pattern_subst(graph, &cond, &subst);
                        
                        // Note: If we don't find a fact matching `id`, this might just be because 
                        //       the fact id isn't canonical. Thus, in the `else if` branch we also 
                        //       check whether there exists a fact id whose canonicalization matches 
                        //       `id`.
                        if let Some(fact_name) = facts.get(&id) {
                            rule = rule.as_str().to_string(); rule.push_str(&fact_name);
                        } else if let Some((_, fact_name)) = facts.iter().find(|(f_id, _)| graph.find_applied_id(f_id) == id) { 
                            rule = rule.as_str().to_string(); rule.push_str(&fact_name);
                        } else if allow_unsat_conditions {
                            rule = rule.as_str().to_string(); rule.push_str("!?");
                        } else {
                            return
                        }
                    }

                    graph.union_instantiations(&template.lhs, &template.rhs, &subst, Some(rule));
                }
            }),
        };
        result.push(rw.into());
    }
    Ok(result)
}