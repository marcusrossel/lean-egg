use egg::*;
use std::collections::VecDeque;
use std::collections::HashMap;
use std::cmp::Ordering;
use crate::lean_expr::*;
use crate::analysis::*;

struct Eta {
    fun: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Eta {

    fn apply_one(&self, egraph: &mut LeanEGraph, eta_class: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let fun_class = subst[self.fun];
        match eta_shift(0, fun_class, egraph, &mut HashMap::new(), rule) {
            ClassState::New(shifted_fun_class) => {
                if egraph.union_trusted(eta_class, shifted_fun_class, rule) {
                    vec![eta_class]
                } else {
                    vec![]
                }
            },
            ClassState::Removed => vec![],
            ClassState::Pending => unreachable!()
        }
    }
}

#[derive(Clone)]
enum ClassState {
    New(Id), 
    Removed,
    Pending
}

// TODO: Prove termination of this function based on the rooted e-graph spanning tree property.
//       The proof should probably somehow reason about the size of the retry queue.

// TODO: Prove that we can simply mutate the e-graph while traversing it without affecting the eta-reduction.
//       I think the reason is that we're only every adding e-nodes but never unioning any e-classes.
//       Thus, any e-node that is added is either already contained in the subgraph rooted at `target_class` 
//       anyway, or will end up in an e-class not contained in the subgraph rooted at `target_class`.

// If a bvar's index is below the threshold, we don't shift it.
// If a bvar's index is above the threshold, then we shift it.
// If a bvar's index equals the `threshold` value, then we remove it. This may entail that bvar's e-class is empty 
// and hence the parent e-node doesn't have sufficient children and also needs to be removed.
fn eta_shift(threshold: u64, target_class: Id, egraph: &mut LeanEGraph, state: &mut HashMap<Id, ClassState>, rule: Symbol) -> ClassState {
    // Optimization: If all of the target's e-nodes contain the bvar value that leads to removal, 
    // the whole class will be removed.
    if egraph[target_class].data.bvars.contains(&threshold) {
        return ClassState::Removed
    }
    
    // * If we already have a new class for the given target, return that.
    // * If the target class contains no applicable e-nodes, i.e. should be removed, propagate that state.
    // * If the target's state is pending, we've looped back onto an e-class. In that case, propagate the pending state
    //   so that the caller can choose a different e-node to explore first. 
    if let Some(target_state) = state.get(&target_class) {
        return target_state.clone()
    }
    
    // If we reach this point, the target e-class has not been visited yet.
    state.insert(target_class, ClassState::Pending);

    // Gets all the nodes in the target e-class and sorts the non-recursive ones to the front.
    let mut nodes = egraph[target_class].nodes.clone();
    nodes.sort_by(|lhs, rhs| nonrec_cmp(lhs, rhs));

    // When a node has a child whose e-class is pending, that node is readded to the end of the queue.
    let mut queue: VecDeque<LeanExpr> = nodes.into();
    let mut new_class: Option<Id> = None;

    'queue_loop: while let Some(node) = queue.pop_front() {
        match node {
            LeanExpr::BVar(e) => {
                // We expect `LeanExpr::BVar`s to always have a `LeanExpr::Nat` child which in turn has a `nat_val`.
                let idx = egraph[e].data.nat_val.unwrap();
                match idx.cmp(&threshold) {
                    Ordering::Less => {
                        let new_node = LeanExpr::Nat(idx); 
                        register_node(&mut new_class, new_node, egraph, state, target_class, rule)
                    }
                    Ordering::Greater => {
                        let new_node = LeanExpr::Nat(idx - 1);
                        register_node(&mut new_class, new_node, egraph, state, target_class, rule);
                    }
                    Ordering::Equal => continue
                }
            },

            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) => {
                // TODO: Is it a problem that we're exploring both paths before checking the result of
                //       the first (aside from being less efficient)?
                let s1 = eta_shift(threshold, ty, egraph, state, rule);
                let s2 = eta_shift(threshold + 1, body, egraph, state, rule);
                match (s1, s2) {
                    (ClassState::New(child1_class), ClassState::New(child2_class)) => {
                        let new_node = swap_children(&node, [child1_class, child2_class]);
                        register_node(&mut new_class, new_node, egraph, state, target_class, rule);
                    },
                    (ClassState::Removed, _) | (_, ClassState::Removed) => continue,
                    (ClassState::Pending, _) | (_, ClassState::Pending) => queue.push_back(node),
                }
            }

            LeanExpr::Const(es) => {
                let mut child_classes = vec![];
                for &e in es.iter() {
                    match eta_shift(threshold, e, egraph, state, rule) {
                        ClassState::New(child_class) => child_classes.push(child_class),
                        ClassState::Removed          => continue 'queue_loop,
                        ClassState::Pending          => { queue.push_back(LeanExpr::Const(es)); continue 'queue_loop }
                    }
                }
                let new_node = LeanExpr::Const(child_classes.into());
                register_node(&mut new_class, new_node, egraph, state, target_class, rule);
            }

            LeanExpr::App([e1, e2]) | LeanExpr::Max([e1, e2]) | LeanExpr::IMax([e1, e2]) => {
                // TODO: Is it a problem that we're exploring both paths before checking the result of
                //       the first (aside from being less efficient)?
                let s1 = eta_shift(threshold, e1, egraph, state, rule);
                let s2 = eta_shift(threshold, e2, egraph, state, rule);
                match (s1, s2) {
                    (ClassState::New(child1_class), ClassState::New(child2_class)) => {
                        let new_node = swap_children(&node, [child1_class, child2_class]);
                        register_node(&mut new_class, new_node, egraph, state, target_class, rule);
                    },
                    (ClassState::Removed, _) | (_, ClassState::Removed) => continue,
                    (ClassState::Pending, _) | (_, ClassState::Pending) => queue.push_back(node),
                }
            },

            LeanExpr::Lit(e) | LeanExpr::FVar(e) | LeanExpr::MVar(e) | LeanExpr::Sort(e) | 
            LeanExpr::UVar(e) | LeanExpr::Param(e) | LeanExpr::Succ(e) => {
                match eta_shift(threshold, e, egraph, state, rule) {
                    ClassState::New(child_class) => {
                        let new_node = swap_child(&node, child_class);
                        register_node(&mut new_class, new_node, egraph, state, target_class, rule);
                    }
                    ClassState::Removed => continue,
                    ClassState::Pending => queue.push_back(node),
                }
            }

            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Erased => 
                register_node(&mut new_class, node, egraph, state, target_class, rule)
        }
    }

    match new_class {
        Some(n) => ClassState::New(n),
        None    => ClassState::Removed
    }
}

fn register_node(new_class: &mut Option<Id>, new_node: LeanExpr, egraph: &mut LeanEGraph, state: &mut HashMap<Id, ClassState>, target_class: Id, rule: Symbol) {
    let node_class = egraph.add(new_node);
    match new_class {
        Some(id) => _ = egraph.union_trusted(*id, node_class, rule),
        None => {
            *new_class = Some(node_class);
            state.insert(target_class, ClassState::New(node_class));
        }
    } 
}

pub fn eta_reduction_rw() -> LeanRewrite {
    rewrite!("!η"; "(λ ?t (app ?f (bvar 0)))" => { Eta { fun : "?f".parse().unwrap() }})
}
