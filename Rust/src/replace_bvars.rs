use egg::*;
use std::collections::HashMap;
use std::collections::HashSet;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::trace::*;

#[derive(Clone)]
pub enum ClassState {
    New(Id),
    Visited(HashSet<LeanExpr>, u64), 
}

impl ToString for ClassState {
    
    fn to_string(&self) -> String {
        match self {
            ClassState::New(id)            => id.to_string(),
            ClassState::Visited(ns, depth) => format!("visited (depth: {}) {:?}", depth, ns.clone().into_iter().collect::<Vec<_>>().sort_by(|lhs, rhs| nonrec_cmp(lhs, rhs)))
        }
    }
}

pub enum Replacement {
    Node(LeanExpr),
    Class(Id)
}

pub fn replace_loose_bvars<C, F: Fn(u64, u64, &mut LeanEGraph, &mut C) -> Replacement>(replace: &F, target_class: Id, egraph: &mut LeanEGraph, rule: Symbol, ctx: &mut C) -> Id {
    dbg_trace("\nStart subst", TraceGroup::Subst);
    let res = replace_loose_bvars_aux(replace, target_class, 0, egraph, &mut HashMap::new(), rule, ctx);
    dbg_trace("End subst\n", TraceGroup::Subst);
    return res
}

// TODO: Prove termination of this function based on the cycle breaking property of e-graphs.

// TODO: Prove that we can simply mutate the e-graph while traversing it without affecting the correcness of substitution.
//       I think the reason is that we're only every adding e-nodes but never unioning any e-classes.
//       (This isn't actually true as we union in `register_node`).
//       Thus, any e-node that is added is either already contained in the subgraph rooted at `target_class` 
//       anyway, or will end up in an e-class not contained in the subgraph rooted at `target_class`.

fn replace_loose_bvars_aux<C, F: Fn(u64, u64, &mut LeanEGraph, &mut C) -> Replacement>(replace: &F, target_class: Id, binder_depth: u64, egraph: &mut LeanEGraph, state: &mut HashMap<Id, ClassState>, rule: Symbol, ctx: &mut C) -> Id { 
    dbg_trace("", TraceGroup::Subst);
    dbg_trace(format!("binder_depth: {}", binder_depth), TraceGroup::Subst);
    dbg_trace(format!("target_class: {}", target_class), TraceGroup::Subst);
    if state.is_empty() {
        dbg_trace("∅".to_string(), TraceGroup::Subst);
    } else {
        for (key, value) in state.clone() { dbg_trace(format!("{} ↦ {}", key, value.to_string()), TraceGroup::Subst); }
    }

    // If we already have a new class for the given target, return that.
    if let Some(ClassState::New(new_class)) = state.get(&target_class) {
        dbg_trace("Early exit: cached new class", TraceGroup::Subst); 
        return new_class.clone()
    }

    // Optimization: If the subgraph rooted at `target_class` doesn't contain any loose bvars, 
    //               we can just return the e-class as is.
    if egraph[target_class].data.loose_bvars.is_empty() {
        dbg_trace("Early exit: no bvars", TraceGroup::Subst); 
        state.insert(target_class, ClassState::New(target_class));
        return target_class
    }
    
    // If the `target_class` has already been visited, we need to make sure to retain its binder depth.
    let mut binder_depth = binder_depth;
    if let Some(ClassState::Visited(_, depth)) = state.get(&target_class) {
        binder_depth = *depth;
    }

    // TODO: I think it might be really inefficient to fix the set of nodes we're going to visit 
    //       *before* the for-loop as this means we could be revisiting nodes unnecessarily when
    //       unrolling the recursion.

    // Gets all the nodes we are going to visit. In e-class cycles, this is reduced by all nodes
    // which have already been visited in a previous cycle. Though, if there are no more available
    // nodes we simply allow all nodes to be visited again.
    let mut nodes: Vec<LeanExpr> = egraph[target_class].nodes.clone().into_iter().filter(|n| 
        match state.get(&target_class) {
            Some(ClassState::Visited(visited, _)) => !visited.contains(n),
            _                                     => true
        }
    ).collect();

    if nodes.is_empty() { 
        state.insert(target_class, ClassState::Visited(HashSet::new(), binder_depth));
        nodes = egraph[target_class].nodes.clone();
    }

    // Sorts the nodes we are going to visit by `nonrec_cmp`.
    // It is important for termination that we visit nodes according to a fixed total order. TODO: Why again?
    // Moving non-recursive e-nodes to the front is simply an optimization as this means
    // that we tend to visit leaves first which reduces the number of iterations we have to
    // take on an e-class cycle.
    nodes.sort_by(|lhs, rhs| nonrec_cmp(lhs, rhs));

    dbg_trace(format!("nodes: {:?}", nodes), TraceGroup::Subst);

    let mut new_class: Option<Id> = None;

    for node in nodes {
        dbg_trace(format!("Entering: {}", node), TraceGroup::Subst);
        visit_node(&node, state, target_class, binder_depth);
        
        match node {
            LeanExpr::BVar(e) => {
                // We expect `LeanExpr::BVar`s to always have a `LeanExpr::Nat` child which in turn has a `nat_val`.
                let idx = egraph[e].data.nat_val.unwrap();
                let replacement = if idx < binder_depth { Replacement::Node(node) } else { replace(idx, binder_depth, egraph, ctx) };
                register_replacement(&mut new_class, replacement, egraph, state, target_class, rule);
            },

            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) => {
                let new_ty = replace_loose_bvars_aux(replace, ty, binder_depth, egraph, state, rule, ctx);
                let new_body = replace_loose_bvars_aux(replace, body, binder_depth + 1, egraph, state, rule, ctx);
                let new_node = swap_children(&node, [new_ty, new_body]);
                register_replacement(&mut new_class, Replacement::Node(new_node), egraph, state, target_class, rule)
            }

            LeanExpr::App([fun, arg]) => {
                let new_fun = replace_loose_bvars_aux(replace, fun, binder_depth, egraph, state, rule, ctx);
                let new_arg = replace_loose_bvars_aux(replace, arg, binder_depth, egraph, state, rule, ctx);
                let new_node = LeanExpr::App([new_fun, new_arg]);
                register_replacement(&mut new_class, Replacement::Node(new_node), egraph, state, target_class, rule)
            },

            _ => register_replacement(&mut new_class, Replacement::Node(node), egraph, state, target_class, rule)
        }
    }

    new_class.unwrap()
}

fn visit_node(node: &LeanExpr, state: &mut HashMap<Id, ClassState>, target_class: Id, binder_depth: u64) {
    match state.get_mut(&target_class) {
        None                                  => _ = state.insert(target_class, ClassState::Visited(HashSet::from([node.clone()]), binder_depth)),
        Some(ClassState::Visited(visited, _)) => _ = visited.insert(node.clone()),
        _                                     => return
    }
}

fn register_replacement(new_class: &mut Option<Id>, replacement: Replacement, egraph: &mut LeanEGraph, state: &mut HashMap<Id, ClassState>, target_class: Id, rule: Symbol) {
    let replacement_class = match replacement {
        Replacement::Class(id) => id,
        Replacement::Node(node) => egraph.add(node)
    };
    match new_class {
        Some(id) => _ = egraph.union_trusted(*id, replacement_class, rule),
        None => {
            *new_class = Some(replacement_class);
            state.insert(target_class, ClassState::New(replacement_class));
        }
    } 
}

pub fn shift_up(offset: u64) -> impl Fn(u64, u64, &mut LeanEGraph, &mut ()) -> Replacement {
    move |idx, binder_depth, egraph, _| {
        if idx < binder_depth { unreachable!() } // `replace_loose_bvars` provides the invariant that `idx >= binder_depth`. 
        Replacement::Node(LeanExpr::BVar(egraph.add(LeanExpr::Nat(idx + offset))))
    }
}