use std::collections::HashMap;
use std::collections::HashSet;
use slotted_egraphs::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;

pub struct RewriteTemplate {
    pub name:  String,
    pub lhs:   Pattern<LeanExpr>,
    pub rhs:   Pattern<LeanExpr>,
    pub conds: Vec<Pattern<LeanExpr>>
}

fn slots_for_node(e: &LeanExpr) -> HashSet<Slot> {
    match e {
        LeanExpr::BVar(s) | LeanExpr::Lam(s, _, _) | LeanExpr::Forall(s, _, _) => HashSet::from([*s]), 
        _ => Default::default()
    }
}
 
fn private_slots(p: &Pattern<LeanExpr>) -> HashSet<Slot> {
    let mut result: HashSet<Slot> = Default::default();
    let mut queue: Vec<&Pattern<LeanExpr>> = vec![p];
    while let Some(next) = queue.pop() {
        match next {
            Pattern::ENode(node, children) => { 
                result.extend(slots_for_node(node));
                queue.extend(children);
            },
            _ => continue
        }
    }
    result
}

fn subst_is_valid(subst: &Subst, illegal_slots: &HashSet<Slot>) -> bool {
    for i in subst.values() {
        for s in i.slots() {
            if illegal_slots.contains(&s) { return false }
        }
    }
    true
}

pub fn templates_to_rewrites(
    templates: Vec<RewriteTemplate>, allow_unsat_conditions: bool
) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let lhs_search = template.lhs.clone();
        let lhs_apply = template.lhs.clone();
        
        let mut illegal_slots = private_slots(&template.lhs);
        illegal_slots.extend(&private_slots(&template.rhs));

        let rw = RewriteT {
            searcher: Box::new(move |graph| { ematch_all(graph, &lhs_search) }),
            applier: Box::new(move |substs, graph| {
                for subst in substs {
                    if !subst_is_valid(&subst, &illegal_slots) { continue; }

                    let lhs = pattern_subst(graph, &lhs_apply, &subst);
                    let analysis: &LeanAnalysis = graph.analysis_data(lhs.id);
                    
                    // Disallows rewriting on primitive e-nodes.
                    if analysis.is_primitive { continue }

                    let mut rule = template.name.clone();
                    
                    for cond in template.conds.clone() {
                        let id = pattern_subst(graph, &cond, &subst);
                        
                        // TODO: Handle conditions.
                    }

                    graph.union_instantiations(&template.lhs, &template.rhs, &subst, Some(rule));
                }
            }),
        };
        result.push(rw.into());
    }
    Ok(result)
}