use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;

struct ToSucc {
    nat_val: Var
}

impl Applier<LeanExpr, LeanAnalysis> for ToSucc {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // This applier is only used in a context where we know that `nat_val` is a `LeanExpr::Nat` and thus has a `nat_val`.
        let nat_val = egraph[subst[self.nat_val]].data.nat_val.unwrap(); 
        // The `ast` is present when explanations are enabled, which we always do.
        let ast = ast.unwrap(); 

        if !(nat_val > 0) { return vec![] }
        let res = format!("(app (const Nat.succ) (lit {}))", nat_val - 1).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
        vec![id]
    }
}

struct OfSucc {
    nat_val: Var
}

impl Applier<LeanExpr, LeanAnalysis> for OfSucc {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // This applier is only used in a context where we know that `nat_val` is a `LeanExpr::Nat` and thus has a `nat_val`.
        let nat_val = egraph[subst[self.nat_val]].data.nat_val.unwrap();
        // The `ast` is present when explanations are enabled, which we always do.
        let ast = ast.unwrap(); 
        
        let res = format!("(lit {})", nat_val + 1).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
        vec![id]
    }
}

pub fn nat_lit_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("!z"; "(lit 0)"                         <=> "(const Nat.zero)"));
    rws.push(       rewrite!("!t"; "(lit ?n)"                        => { ToSucc { nat_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("!o"; "(app (const Nat.succ) (lit ?n))" => { OfSucc { nat_val : "?n".parse().unwrap() }}));
    rws
}
