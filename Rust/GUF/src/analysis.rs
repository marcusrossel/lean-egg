use std::cell::Cell;
use std::collections::HashSet;
use rs2::*;
use crate::egraph::*;
use crate::lean_expr::*;
use crate::proof::*;
use crate::util::*;

#[derive(Debug, Clone)]
pub struct LeanAnalysisData {
    pub nat_val:      Option<u64>,
    pub dir_val:      Option<bool>,
    pub loose_bvars:  HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
}

impl Default for LeanAnalysisData {

    fn default() -> Self {
        LeanAnalysisData {
            nat_val: None,
            dir_val: None,
            loose_bvars: HashSet::default(),
        }
    }
}

thread_local! {
    // GUF's analyses are stateless, so the configuration of `LeanAnalysis` is set per thread.
    static UNION_SEMANTICS: Cell<bool> = Cell::new(true);
}

pub struct LeanAnalysis;

impl LeanAnalysis {
    pub fn loose_bvar_idx_limit() -> u64 { 100 }

    pub fn set_union_semantics(union_semantics: bool) {
        UNION_SEMANTICS.set(union_semantics)
    }
}

impl Semilattice for LeanAnalysisData {
    type G = Proof;

    // Equal terms have the same analysis data.
    fn act(_: &Proof, data: &Self) -> Self {
        data.clone()
    }

    fn merge(&mut self, from: Self) -> bool {
        let loose_bvar_m = if UNION_SEMANTICS.get() {
            union_sets(&mut self.loose_bvars, from.loose_bvars)
        } else {
            intersect_sets(&mut self.loose_bvars, from.loose_bvars)
        };

        // `merge_max` prefers `Some` value over `None`. Note that if `self` and `from` both have
        // nat values, then they should have the *same* value as otherwise merging their e-classes
        // indicates an invalid rewrite. The same applies for the `dir_val`s.
        merge_max(&mut self.nat_val, from.nat_val) |
        merge_max(&mut self.dir_val, from.dir_val) |
        loose_bvar_m
    }

    // We don't care about proofs of `t = t`, so we treat all of them as known.
    fn insert_self_edge(&mut self, _: Proof) {}
    fn contains_self_edge(&self, _: &Proof) -> bool { true }
}

impl Analysis for LeanAnalysis {
    type G = Proof;
    type S = LeanAnalysisData;
    type L = LeanExpr;

    fn canon(enode: &LeanExpr, uf: &Unionfind<LeanAnalysisData>) -> (Proof, Either<LeanExpr, Id>) {
        let mut enode = enode.clone();
        let mut proofs = vec![];
        for child in enode.children_mut() {
            let (proof, id) = uf.find(child.clone());
            proofs.push(proof);
            *child = (Proof::identity(), id);
        }
        (Proof::congr(proofs), Either::L(enode))
    }

    fn mk(enode: &LeanExpr, id: Id, uf: &Unionfind<LeanAnalysisData>) -> LeanAnalysisData {
        record_enode(enode, id);
        let data = |child: &PId| class_data(uf, child);

        match enode {
            LeanExpr::Nat(n) =>
                LeanAnalysisData {
                    nat_val: Some(*n),
                    ..Default::default()
                },

            LeanExpr::Str(shift_up) if shift_up == "+" =>
                LeanAnalysisData {
                    dir_val: Some(true),
                    ..Default::default()
                },

            LeanExpr::Str(shift_down) if shift_down == "-" =>
                LeanAnalysisData {
                    dir_val: Some(false),
                    ..Default::default()
                },

            LeanExpr::Str(_) | LeanExpr::Fun(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) |
            LeanExpr::Succ(_) | LeanExpr::Max(_) | LeanExpr::IMax(_) | LeanExpr::Fact(_) |
            LeanExpr::Unknown =>
                LeanAnalysisData {
                    ..Default::default()
                },

            LeanExpr::BVar(idx) =>
                LeanAnalysisData {
                    loose_bvars: match data(idx).nat_val {
                        Some(n) => vec![n].into_iter().collect(),
                        None    => HashSet::new()
                    },
                    ..Default::default()
                },

            LeanExpr::App([fun, arg]) =>
                LeanAnalysisData {
                    loose_bvars: union_clone(&data(fun).loose_bvars, &data(arg).loose_bvars),
                    ..Default::default()
                },

            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) =>
                LeanAnalysisData {
                    loose_bvars: union_clone(
                        &data(ty).loose_bvars,
                        &shift_down(&data(body).loose_bvars)
                    ),
                    ..Default::default()
                },

            LeanExpr::Subst([idx, to, e]) => {
                let mut loose_bvars = data(e).loose_bvars.clone();
                loose_bvars.remove(&data(idx).nat_val.unwrap());
                loose_bvars.extend(&data(to).loose_bvars);
                LeanAnalysisData { loose_bvars, ..Default::default() }
            },

            LeanExpr::Shift([dir, off, cut, e]) => {
                let dir_is_up = data(dir).dir_val.unwrap();
                let off = data(off).nat_val.unwrap();
                let cut = data(cut).nat_val.unwrap();
                let mut loose_bvars: HashSet<u64> = Default::default();
                for &b in data(e).loose_bvars.iter() {
                    // TODO: Only do this when union semantics are active.
                    if b > Self::loose_bvar_idx_limit() { continue; }

                    if b < cut {
                        loose_bvars.insert(b);
                    } else if dir_is_up {
                        loose_bvars.insert(b + off);
                    } else if off <= b {
                        // If `off > b`, this shift was "not intended", so we just don't do it.
                        loose_bvars.insert(b - off);
                    }
                }

                LeanAnalysisData { loose_bvars, ..Default::default() }
            },

            LeanExpr::Shaped([_, e]) | LeanExpr::Proof(e) | LeanExpr::Inst(e) =>
                LeanAnalysisData {
                    loose_bvars: data(e).loose_bvars.clone(),
                    ..Default::default()
                },

            LeanExpr::Eq([l, r]) =>
                LeanAnalysisData {
                    loose_bvars: union_clone(&data(l).loose_bvars, &data(r).loose_bvars),
                    ..Default::default()
                },

            _ => Default::default()
        }
    }

    fn children_mut(enode: &mut LeanExpr) -> Box<[&mut PId]> {
        enode.children_mut().iter_mut().collect()
    }

    fn prettyprint(enode: &LeanExpr, child_strings: Box<[String]>) -> String {
        prettyprint(enode, child_strings)
    }

    fn ematch(egraph: &LeanEGraph, id: Id, pat: &LeanPattern) -> Vec<LeanSubst> {
        skeleton_ematch(egraph, id, pat).into_iter().map(|(subst, _)| {
            subst.into_iter().map(|(var, id)| (var, (Proof::identity(), id))).collect()
        }).collect()
    }
}

// Returns the analysis data of the e-class of `x`.
pub fn class_data<'a>(uf: &'a Unionfind<LeanAnalysisData>, x: &PId) -> &'a LeanAnalysisData {
    uf.get_leader_semilattice(uf.find(x.clone()).1)
}

pub trait EClassData {
    // Analogous to `egraph[x].data` in egg.
    fn data(&self, x: &PId) -> &LeanAnalysisData;
}

impl EClassData for LeanEGraph {

    fn data(&self, x: &PId) -> &LeanAnalysisData {
        class_data(&self.uf, x)
    }
}

pub type LeanEGraph  = EGraph<LeanAnalysis>;
pub type LeanRewrite = Rule<LeanAnalysis>;
pub type LeanPattern = Pattern<LeanAnalysis>;
pub type LeanTerm    = Term<LeanAnalysis>;
pub type LeanSubst   = Subst<LeanAnalysis>;
