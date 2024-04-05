use egg::*;
use std::collections::HashMap;
use std::collections::HashSet;
use indexmap::IndexSet;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::trace::*;

// Binder depth.
type Depth := u64;

// Identifiers of e-classes already present in an e-graph prior to any substitution.
type SrcId := Id;

// Identifiers of substitute e-classes. That is, those e-classes which are created
// during substitution.
type SubId := Id;

// An index of an e-node in `Context.todo`.
type TodoIdx := usize;

// A bound variable substitute is what is returned by the bound variables substitution function
// used with `subst`. The `class` will be merged into the bound variables substitute class. A
// simple example of this is a class containing just a single e-node, like a shifted bound variable.
// If the `class` is constructed in a more complex manner, all unions which occur as part of this
// construction should be delayed, as they might otherwise affect the traversal of `subst`. They
// should therefore be passed along in the `unions`, which are performed at the end of `subst`.
pub struct BVarSub {
    pub class: SubId,
    pub unions: HashMap<SubId, HashSet<SubId>>
}

// A "target" is an e-class at a specific binder depth. These two values need to be 
// considered together so often during substitution that we given them an own type.
#[derive(PartialEq, Eq, Hash, Clone)]
struct Target {
    class: SrcId, 
    depth: Depth
}

// Various data required for bookkeeping during substitution.
#[derive(Default)]
struct Context {
    // When an e-class `c` is visited at a binder depth `d` and continues on to visit child e-classes, 
    // this map records that `c` is work-in-progress for depth `d`. Note that a given e-class can be
    // work-in-progress for multiple binder depths at once.
    wip: HashMap<SrcId, HashSet<Depth>>,               
    // The substitution map maps a given e-class target to a new substituted e-class.
    sub: HashMap<Target, SubId>,
    // The set of unions that need to be performed after the main DFS of subsitution has completed.
    // For each `unions.get(c) = Some cs`, the unions need to be performed for all e-classes in `{c} ∪ cs`.
    unions: HashMap<SubId, HashSet<SubId>>,   
    // The set of e-nodes which are waiting for other e-classes to be subsituted before being able to
    // be substituted themselves. An e-node appears in this set, when it tried to substitute a child 
    // e-class which is work-in-progress (see `Context.wip`). That is, when there's a loop in the e-graph.
    // The e-node is stored together with the e-class target to which it belongs.
    // A todo e-node is then processed when all of its dependencies are registered in `Context.sub`. 
    // This is in part tracked by `Contet.wait` and `Context.deps`.
    todo: IndexSet<(LeanExpr, Target)>,
    // The number of child e-classes a given todo e-node is waiting on. When this becomes 0, the e-node 
    // is processed.
    wait: HashMap<TodoIdx, usize>,  
    // A map from e-class targets to those todo e-nodes waiting on the given target. When a given target 
    // is registered in `Context.sub`, the `Context.wait` of all dependents is updated.
    deps: HashMap<Target, HashSet<TodoIdx>>  
}

// Creates a new e-class which is the same as the given `class` but substitutes all loose bound variables 
// in its sub-graph according to the given substitution function.
pub fn subst<B>(class: SrcId, graph: &mut LeanEGraph, reason: Symbol, bvar_subst: &B) -> SubId 
where B : Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    let (s, u) = subst_without_unions(class, graph, bvar_subst);
    perform_unions(u, reason, graph);
    return s
}

// Same as `subst` but returns the generated unions instead of performing them.
pub fn subst_without_unions<B>(class: SrcId, graph: &mut LeanEGraph, bvar_subst: &B) -> (SubId, HashMap<SubId, HashSet<SubId>>)
where B : Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    let tgt = Target { class, depth: 0 };
    let mut ctx: Context = Default::default();
    let s = subst_core(&tgt, &mut ctx, graph, bvar_subst).unwrap();
    return (s, ctx.unions)
}

// TODO: This might be the function in which to control justification propagation.
fn perform_unions(unions: HashMap<SubId, HashSet<SubId>>, reason: Symbol, graph: &mut LeanEGraph) {
    for (class, equivs) in unions.iter() {
        for other in equivs {
            graph.union_trusted(*class, *other, reason);
        }
    }
}

// When this function returns `None`, that means that a substitution for the given 
// e-class target could not yet be created.
fn subst_core<B>(tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph, bvar_subst: &B) -> Option<SubId> 
where B : Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    if let Some(&s) = ctx.sub.get(tgt) {
        // If the given e-class target has already been substituted, 
        // return the substitute immediately.
        return Some(s)
    } else if graph[tgt.class].data.max_loose_bvar() < Some(tgt.depth) {
        // If the given e-class target does not contain any loose bound variables
        // which are large enough to escape the outermost binder of the subsitution's
        // root e-class, we can just keep it as is. It is still important that we record 
        // this in `ctx.sub`, as processing of todos assumes that all of the todo's children 
        // have substitutes registered in `ctx.sub`.
        ctx.sub.insert(tgt.clone(), tgt.class);
        return Some(tgt.class)
    } else if ctx.wip.get(&tgt.class).is_some_and(|w| w.contains(&tgt.depth)) {
        // If the e-class target is already WIP, we have reached a proper loop (one where
        // the binder depth does not increase on each iteration) and return `None` to
        // indicate this to the caller.
        return None
    } else {
        // If none of the previous branches apply, we are visiting the given e-class target
        // for the first time. Thus, we first mark it as WIP.
        _ = ctx.wip.entry(tgt.class).or_insert(HashSet::new()).insert(tgt.depth);
        subst_core_new_target(tgt, ctx, graph, bvar_subst)
    }
}

// Implementation detail of `subst_core`.
fn subst_core_new_target<B>(tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph, bvar_subst: &B) -> Option<SubId> 
where B : Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    // Gets and sorts the nodes we are going to visit by `nonrec_cmp`. Moving non-recursive 
    // e-nodes to the  front is simply an optimization as this means that we tend to visit 
    // leaves first which reduces the number of todo e-nodes and corresponding callbacks.
    let mut nodes = graph[tgt.class].nodes.clone();
    nodes.sort_by(|lhs, rhs| lhs.rec_cmp(rhs));

    for node in nodes {
        if let Some(bvar_idx) = node.bvar_idx() {
            let idx_val = graph[*bvar_idx].data.nat_val.unwrap();
            // Only runs the bound variable substitution if the bound variable is loose.
            if idx_val >= tgt.depth { 
                let BVarSub { class: s, unions: u } = bvar_subst(idx_val, tgt.depth, graph);
                add_subst_class(s, tgt, ctx, graph);
                ctx.unions.extend(u);
            } else { 
                add_subst_node(node, tgt, ctx, graph);
            };
        } else if node.is_rec() {
            subst_recursive_node(&node, tgt, ctx, graph, bvar_subst);
        } else {
            add_subst_node(node, tgt, ctx, graph);
        }
    }
    
    // If all e-nodes remain todos, this returns `None`, indicating to the caller that this e-class 
    // target remains WIP. Otherwise, a substitute e-class for `tgt` must have been created and 
    // registered in `ctx.sub`, which we thus return.
    ctx.sub.get(tgt).copied()
}

// Implementation detail of `subst_core_new_target`.
//
// Tries to construct the substitution of a given e-node which is expected to be recursive.
// If this is successful, the substitute is added to the substitute e-class in `ctx.sub`.
// If it fails, the e-node is registered as a todo node.
fn subst_recursive_node<B>(rec_node: &LeanExpr, tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph, bvar_subst: &B)
where B : Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    let mut sub_node = rec_node.clone();
    let mut pending = HashSet::<Target>::new();

    for (idx, child) in sub_node.children_mut().iter_mut().enumerate() {
        // The depth is increased by 1 if the child is the body of a binder.
        let depth = if idx == 1 && rec_node.is_binder() { tgt.depth + 1 } else { tgt.depth };
        let child_tgt = Target { class: *child, depth: depth };
        // If the substitution of the child works, replace the child with its substitute in `sub_node`.
        // Otherwise, record the given child target as being pending.
        if let Some(child_sub) = subst_core(&child_tgt, ctx, graph, bvar_subst) {
            *child = child_sub;
        } else {
            pending.insert(child_tgt);
        }
    }

    // If all children could be substituted, add the then completely substituted `sub_node` as
    // a new node for `tgt`. Else, add the pending children as todos for `rec_node`.
    if pending.is_empty() {
        add_subst_node(sub_node, tgt, ctx, graph);
    } else {
        add_todo(rec_node, pending, tgt, ctx);
    }
}

// Adds the given (substituted) e-node to the substitute e-class of the given e-class target.
// If that substitute e-class does not exist yet, it is created and the todo e-nodes are updated.
fn add_subst_node(node: LeanExpr, tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph) {
    let node_class = graph.add(node);
    add_subst_class(node_class, tgt, ctx, graph);
}

// Merges the given (substituted) e-class into the substitute e-class of the given e-class target.
// If that substitute e-class does not exist yet, it is created and the todo e-nodes are updated.
fn add_subst_class(class: SubId, tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph) {
    if let Some(&s) = ctx.sub.get(tgt) {
        // If the given e-class target already has a substitute, simply record the new class
        // as requiring a union with that substitute e-class.
        ctx.unions.entry(s).or_insert(HashSet::new()).insert(class);
    } else {
        // If the given class is the first substitute for the given e-class target, 
        // create the substitute e-class from it.
        ctx.sub.insert(tgt.clone(), class);
        // When a new substitute e-class is created, the todo e-nodes need to be updated.
        update_todos(tgt, ctx, graph);
    }
}

// Updates the todo e-nodes depending on a given newly substituted e-class target.
// This can might only reduce the e-nodes' waits, or, if the wait becomes 0, lead 
// to the e-node being processed.
fn update_todos(tgt: &Target, ctx: &mut Context, graph: &mut LeanEGraph) {
    // Get the set of todo e-nodes depending on the given e-class target.
    // If this set is empty (absent), nothing needs to be done.
    if let Some(deps) = ctx.deps.remove(tgt) {
        for dep in deps {
            // We assume any given todo e-node to have an associated wait.
            let new_wait = ctx.wait.get(&dep).unwrap() - 1;
            if new_wait == 0 {
                // If the new wait is 0, then all of the todo e-node's children have
                // substitute e-classes and the e-node can be processed.
                ctx.wait.remove(&dep);
                process_todo(dep, ctx, graph);
            } else {
                // If the new wait is still not 0, the todo e-node must continue
                // to wait.
                ctx.wait.insert(dep, new_wait);
            }
        }
    }
}

// Performs substitution of the the given todo e-node under the assumption that
// `ctx.sub` contains substitutes for all dependencies.
fn process_todo(todo: TodoIdx, ctx: &mut Context, graph: &mut LeanEGraph) {
    // We assume any given todo e-node to have an entry in the `todo` set.
    let (node, tgt) = ctx.todo.get_index(todo).unwrap().clone();
    
    // A todo can only be an application-, lambda- or forall-node.
    let mut sub_node = node.clone();
    for (idx, child) in sub_node.children_mut().iter_mut().enumerate() {
        // The depth is increased by 1 if the child is the body of a binder.
        let depth = if idx == 1 && node.is_binder() { tgt.depth + 1 } else { tgt.depth };
        let child_tgt = Target { class: *child, depth: depth };
        // The substitutes of children of a todo node are expected to be present 
        // when this function (`process_todo`) is called.
        if let Some(&child_sub) = ctx.sub.get(&child_tgt) {
            *child = child_sub;
        } else {
            panic!("'process_todo' tried to access absent substitute child #{} of node {:?}", idx, node);
        }
        
    }

    add_subst_node(sub_node, &tgt, ctx, graph);
}

fn add_todo(node: &LeanExpr, deps: HashSet<Target>, tgt: &Target, ctx: &mut Context) {
    // If the given node is already a todo for the given e-class target, 
    // then nothing more needs to be done.
    let (todo, is_new) = ctx.todo.insert_full((node.clone(), tgt.clone()));
    if !is_new { return }

    // The number of dependencies that need to be waited on is exactly the number of
    // elements in `deps`.
    ctx.wait.insert(todo, deps.len());

    // Add the todo to the dependency list of each of its dependencies. That way, when
    // the dependencies are resolved, the todo is processed. 
    for dep in deps {
        ctx.deps.entry(dep).or_insert(HashSet::new()).insert(todo);
    }
}
    