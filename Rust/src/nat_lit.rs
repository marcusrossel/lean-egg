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

        // TODO: We can't activate this assertion, because then egg can crashs from unsound rewrites (cf. `Tests/Soundness.lean`).
        //       Is there a way to gracefully fail?
        // 
        // if let (Some(t), Some(f)) = (*to, from) { assert_eq!(t, f) }

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

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            if lit_val > 0 {
                let ast = ast.unwrap(); // The `ast` is present when explanations are enabled, which we always do.
                let res = format!("(app (const Nat.succ) (lit {}))", lit_val - 1).parse().unwrap();
                let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
                return vec![id]
            }
        }
        vec![]
    }
}

struct OfSucc {
    lit_val: Var
}

impl Applier<LeanExpr, NatLitAnalysis> for OfSucc {

    fn apply_one(&self, egraph: &mut EGraph<LeanExpr, NatLitAnalysis>, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        if let Some(lit_val) = egraph[subst[self.lit_val]].data {
            let ast = ast.unwrap(); // The `ast` is present when explanations are enabled, which we always do.
            let res = format!("(lit {})", lit_val + 1).parse().unwrap();
            let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
            return vec![id]
        }
        vec![]
    }
}

pub fn nat_lit_rws() -> Vec<Rewrite<LeanExpr, NatLitAnalysis>> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("!z"; "(lit 0)"                         <=> "(const Nat.zero)"));
    rws.push(       rewrite!("!t"; "(lit ?n)"                        => { ToSucc { lit_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("!o"; "(app (const Nat.succ) (lit ?n))" => { OfSucc { lit_val : "?n".parse().unwrap() }}));
    rws
}
