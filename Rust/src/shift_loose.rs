use std::cmp::Ordering;
use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::subst::*;

pub enum Offset {
    Up(u64),
    Down(u64)
}

impl Offset {

    pub fn diff(lhs: u64, rhs: u64) -> Self {
        if lhs >= rhs {
            Offset::Up(lhs - rhs)
        } else {
            Offset::Down(rhs - lhs)
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Offset::Up(o) | Offset::Down(o) => *o == 0
        }
    }
}

pub fn shift_loose_bvars(offset: Offset, target_class: Id, panic_on_bvar_0: bool, reason: Symbol, graph: &mut LeanEGraph) -> Id {
    let (s, u) = shift_loose_bvars_without_unions(offset, target_class, panic_on_bvar_0, graph);
    perform_unions(u, reason, graph);
    s
}

pub fn shift_loose_bvars_without_unions(offset: Offset, target_class: Id, panic_on_bvar_0: bool, graph: &mut LeanEGraph) -> (Id, Unions) {
    subst_without_unions(target_class, graph, &shift_loose_bvar(offset, panic_on_bvar_0))
}

fn shift_loose_bvar(offset: Offset, panic_on_bvar_0: bool) -> impl Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    move |idx, binder_depth, graph| {
        match (idx.cmp(&binder_depth), panic_on_bvar_0) {
            (Ordering::Greater, _) | (Ordering::Equal, false) => {
                let shifted_idx = match offset {
                    Offset::Up(o)   => idx + o,
                    Offset::Down(o) => idx - o
                };
                let idx_class = graph.add(LeanExpr::Nat(shifted_idx));
                let bvar_class = graph.add(LeanExpr::BVar(idx_class));
                BVarSub { class: bvar_class, unions: Default::default() }
            },
            (Ordering::Equal, true) => panic!(),
            // `subst` provides the invariant that `idx >= binder_depth`.
            (Ordering::Less, _) => unreachable!(), 
        }
    }
}