use egg::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::Ordering;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::util::*;

struct Beta {
    body: Var,
    arg: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Beta {

    fn apply_one(&self, egraph: &mut LeanEGraph, beta_class: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let body_class = subst[self.body];
        let arg_class = subst[self.arg];
        let substituted_body_class = beta_reduce(0, body_class, arg_class, egraph, &mut HashMap::new(), rule);
        if egraph.union_trusted(beta_class, substituted_body_class, rule) {
            vec![beta_class]
        } else {
            vec![]
        }
    }
}

#[derive(Clone)]
enum ClassState {
    New(Id),
    Visited(HashSet<LeanExpr>), 
}

impl ToString for ClassState {
    
    fn to_string(&self) -> String {
        match self {
            ClassState::New(id)     => id.to_string(),
            ClassState::Visited(ns) => format!("visited {:?}", ns.clone().into_iter().collect::<Vec<_>>().sort_by(|lhs, rhs| nonrec_cmp(lhs, rhs)))
        }
    }
}

// TODO: Prove termination of this function based on the rooted e-graph spanning tree property.
//       The proof should probably somehow reason about the size of the retry queue.

// TODO: Prove that we can simply mutate the e-graph while traversing it without affecting the eta-reduction.
//       I think the reason is that we're only every adding e-nodes but never unioning any e-classes.
//       (This isn't actually true as we union in `register_node`).
//       Thus, any e-node that is added is either already contained in the subgraph rooted at `target_class` 
//       anyway, or will end up in an e-class not contained in the subgraph rooted at `target_class`.

fn beta_reduce(subst_idx: u64, body_class: Id, arg_class: Id, egraph: &mut LeanEGraph, state: &mut HashMap<Id, ClassState>, rule: Symbol) -> Id { 
    dbg_trace("");
    dbg_trace(format!("subst_idx: {}", subst_idx));
    dbg_trace(format!("body_class: {}", body_class));
    dbg_trace(format!("arg_class: {}", arg_class));
    if state.is_empty() {
        dbg_trace("∅".to_string());
    } else {
        for (key, value) in state.clone() { dbg_trace(format!("{} ↦ {}", key, value.to_string())); }
    }

    // If we already have a new class for the given body, return that.
    if let Some(ClassState::New(new_class)) = state.get(&body_class) {
        dbg_trace("Early exit: cached new class"); 
        return new_class.clone()
    }

    // Optimization: If the subgraph rooted at `body_class` doesn't contain any reference to a bvar
    //               whose index is the `subst_idx`, we can return it as is.
    if !egraph[body_class].data.bvars.contains(&subst_idx) {
        dbg_trace("Early exit: no bvars with substitution index"); 
        state.insert(body_class, ClassState::New(body_class));
        return body_class
    }
    
    // TODO: I think it might be really inefficient to fix the set of nodes we're going to visit 
    //       *before* the for-loop as this means we could be revisiting nodes unnecessarily when
    //       unrolling the recursion. We might also not want to be sharing which nodes have been
    //       visited for a given e-class but rather keep that local like the `threshold`.

    // Gets all the nodes we are going to visit. In e-class cycles, this is reduced by all nodes
    // which have already been visited in a previous cycle. Though, if there are no more available
    // nodes we simply allow all nodes to be visited again.
    let mut nodes: Vec<LeanExpr> = egraph[body_class].nodes.clone().into_iter().filter(|n| 
        match state.get(&body_class) {
            Some(ClassState::Visited(visited)) => !visited.contains(n),
            _                                  => true
        }
    ).collect();
    if nodes.is_empty() { nodes = egraph[body_class].nodes.clone() }

    // Sorts the nodes we are going to visit by `nonrec_cmp`.
    // It is important for termination that we visit nodes according to a fixed total order. 
    // Moving non-recursive e-nodes to the front is simply an optimization as this means
    // that we tend to visit leaves first which reduces the number of iterations we have to
    // take on an e-class cycle.
    nodes.sort_by(|lhs, rhs| nonrec_cmp(lhs, rhs));

    dbg_trace(format!("nodes: {:?}", nodes)); 

    let mut new_class: Option<Id> = None;

    for node in nodes {
        dbg_trace(format!("Entering: {}", node));
        visit_node(&node, state, body_class);
        
        match node {
            LeanExpr::BVar(e) => {
                // We expect `LeanExpr::BVar`s to always have a `LeanExpr::Nat` child which in turn has a `nat_val`.
                let idx = egraph[e].data.nat_val.unwrap();
                match idx.cmp(&subst_idx) {
                    Ordering::Less => {
                        // TODO: Optimize this branch by using the existing `target_class` as the new class. 
                        let idx_node = LeanExpr::Nat(idx); 
                        let idx_class = egraph.add(idx_node);
                        let new_node = LeanExpr::BVar(idx_class);
                        register_node(&mut new_class, new_node, egraph, state, body_class, rule)
                    }
                    Ordering::Greater => {
                        let idx_node = LeanExpr::Nat(idx - 1); 
                        let idx_class = egraph.add(idx_node);
                        let new_node = LeanExpr::BVar(idx_class);
                        register_node(&mut new_class, new_node, egraph, state, body_class, rule);
                    }
                    Ordering::Equal => {
                        continue
                        // TODO:
                        // substitute for the arg_class
                        // when substitution in arg_class:
                        // * local vars shouldn't be shifted (i.e. those that are < threshold starting at thresh 0)
                        // * loose bvars should by shifted `-subst_idx - 1`.
                        //
                        // we can probably slightly generalize the `eta_shift` function for this so that we can
                        // use it for this shifting
                        //let shifted_arg_class: Id = todo!();
                        // TODO: This is `register_node` but without creating a single node class and instead using
                        //       `shifted_arg_class` in that position.
                        // match new_class {
                        //     Some(id) => _ = egraph.union_trusted(id, shifted_arg_class, rule),
                        //     None => {
                        //         new_class = Some(shifted_arg_class);
                        //         state.insert(body_class, ClassState::New(shifted_arg_class));
                        //     }
                        // } 
                    }
                }
            },

            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) => {
                let reduced_ty   = beta_reduce(subst_idx, ty, arg_class, egraph, state, rule);
                let reduced_body = beta_reduce(subst_idx + 1, body, arg_class, egraph, state, rule);
                let new_node = swap_children(&node, [reduced_ty, reduced_body]);
                register_node(&mut new_class, new_node, egraph, state, body_class, rule)
            }

            LeanExpr::Const(es) => {
                let reduced_children = es.iter().map(|e| beta_reduce(subst_idx, *e, arg_class, egraph, state, rule));
                let new_node = LeanExpr::Const(reduced_children.collect());
                register_node(&mut new_class, new_node, egraph, state, body_class, rule);
            }

            LeanExpr::App([e1, e2]) | LeanExpr::Max([e1, e2]) | LeanExpr::IMax([e1, e2]) => {
                let r1 = beta_reduce(subst_idx, e1, arg_class, egraph, state, rule);
                let r2 = beta_reduce(subst_idx, e2, arg_class, egraph, state, rule);
                let new_node = swap_children(&node, [r1, r2]);
                register_node(&mut new_class, new_node, egraph, state, body_class, rule)
            },

            LeanExpr::Lit(e) | LeanExpr::FVar(e) | LeanExpr::MVar(e) | LeanExpr::Sort(e) | 
            LeanExpr::UVar(e) | LeanExpr::Param(e) | LeanExpr::Succ(e) => {
                let reduced_child = beta_reduce(subst_idx, e, arg_class, egraph, state, rule);
                let new_node = swap_child(&node, reduced_child);
                register_node(&mut new_class, new_node, egraph, state, body_class, rule);
            }

            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Erased =>
                register_node(&mut new_class, node, egraph, state, body_class, rule)
        }
    }

    new_class.unwrap()
}

fn visit_node(node: &LeanExpr, state: &mut HashMap<Id, ClassState>, target_class: Id) {
    match state.get_mut(&target_class) {
        None                               => _ = state.insert(target_class, ClassState::Visited(HashSet::from([node.clone()]))),
        Some(ClassState::Visited(visited)) => _ = visited.insert(node.clone()),
        _                                  => return
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

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("!β"; "(app (λ ?t ?b) ?a)" => { Beta { body : "?b".parse().unwrap(), arg : "?a".parse().unwrap() }})
}
