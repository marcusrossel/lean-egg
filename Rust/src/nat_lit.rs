use egg::*;
use crate::lean_expr::*;

#[derive(Default)]
pub struct NatLitAnalysis;
impl Analysis<LeanExpr> for NatLitAnalysis {
    type Data = Option<u64>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        // This prefers `Some` value over `None`. Note that if `to` and `from` are both present,
        // then they should have the same value as otherwise the merging of their e-classes indicates 
        // an invalid rewrite.
        egg::merge_max(to, from)
    }

    // Note: We also assign all `Nat` nodes a value, but that shouldn't be a problem as different `Nat` 
    //       nodes should never belong to the same e-class.
    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {
        match enode {
            LeanExpr::Nat(n) => Some(*n),
            LeanExpr::Lit(l) => egraph[*l].data,
            _ => None
        }
    }
}

struct ToSucc {
    lit_val: Var
}

impl Applier<LeanExpr, NatLitAnalysis> for ToSucc {

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, matched_id: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, _: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            if lit_val > 0 {
                let pred = egraph.add(LeanExpr::Nat(lit_val - 1));
                let pred_lit = egraph.add(LeanExpr::Lit(pred));
                let succ_name = egraph.add(LeanExpr::Str("Nat.succ".to_string()));
                let succ_const = egraph.add(LeanExpr::Const(Box::new([succ_name])));
                let app_succ_pred = egraph.add(LeanExpr::App([succ_const, pred_lit]));
                if egraph.union(matched_id, app_succ_pred) {
                    return vec![app_succ_pred]
                } 
            }
        }
        vec![]
    }
}

struct OfSucc {
    lit_val: Var
}

impl Applier<LeanExpr, NatLitAnalysis> for OfSucc {

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, matched_id: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, _: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            let succ = egraph.add(LeanExpr::Nat(lit_val + 1));
            let succ_lit = egraph.add(LeanExpr::Lit(succ));
            if egraph.union(matched_id, succ_lit) {
                return vec![succ_lit]
            } 
        }
        vec![]
    }
}

// TODO: Mention in the thesis that this uses dynamic rewrites, which is also why we can't implement it 
//       as a `Egg.Rewrite` in Lean.
pub fn nat_lit_rws() -> Vec<Rewrite<LeanExpr, NatLitAnalysis>> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("!z"; "(lit 0)"                         <=> "(const Nat.zero)"));
    rws.push(       rewrite!("!t"; "(lit ?n)"                        => { ToSucc { lit_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("!o"; "(app (const Nat.succ) (lit ?n))" => { OfSucc { lit_val : "?n".parse().unwrap() }}));
    rws
}
