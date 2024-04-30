use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use std::ops::*;

struct ToSucc {
    nat_val: Var
}

impl Applier<LeanExpr, LeanAnalysis> for ToSucc {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // This applier matches against "lit ?n", which means that `?n` might be a string.
        if let Some(nat_val) = egraph[subst[self.nat_val]].data.nat_val {
            // The `ast` is present when explanations are enabled, which we always do.
            let ast = ast.unwrap(); 

            if !(nat_val > 0) { return vec![] }
            let res = format!("(app (const Nat.succ) (lit {}))", nat_val - 1).parse().unwrap();
            let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
            vec![id]
        } else {
            vec![]
        }
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

struct Op {
    lhs_nat_val: Var,
    rhs_nat_val: Var,
    op: fn(u64, u64) -> u64
}

impl Applier<LeanExpr, LeanAnalysis> for Op {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // This applier is only used in a context where we know that `nat_val` is a `LeanExpr::Nat` and thus has a `nat_val`.
        let lhs = egraph[subst[self.lhs_nat_val]].data.nat_val.unwrap();
        let rhs = egraph[subst[self.rhs_nat_val]].data.nat_val.unwrap();
        // The `ast` is present when explanations are enabled, which we always do.
        let ast = ast.unwrap(); 
        
        let val = (self.op)(lhs, rhs);
        let res = format!("(lit {})", val).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast, &res, subst, rule);
        vec![id]
    }
}

// The supported internalizations can be found at:
// https://github.com/leanprover/lean4/blob/1e74c6a348416677987cd71a59a451db0aef9e26/src/kernel/type_checker.cpp#L1138
pub fn nat_lit_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("≡0";  "(lit 0)"                                      <=> "(const Nat.zero)"));
    rws.push(       rewrite!("≡→S"; "(lit ?n)"                                      => { ToSucc { nat_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("≡S→"; "(app (const Nat.succ) (lit ?n))"               => { OfSucc { nat_val : "?n".parse().unwrap() }}));
    rws.push(       rewrite!("≡+";  "(app (app (const Nat.add) (lit ?l)) (lit ?r))" => { Op { op: u64::add,            lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws.push(       rewrite!("≡-";  "(app (app (const Nat.sub) (lit ?l)) (lit ?r))" => { Op { op: u64::saturating_sub, lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws.push(       rewrite!("≡*";  "(app (app (const Nat.mul) (lit ?l)) (lit ?r))" => { Op { op: u64::mul,            lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws.push(       rewrite!("≡^";  "(app (app (const Nat.pow) (lit ?l)) (lit ?r))" => { Op { op: u64_pow,             lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws.push(       rewrite!("≡/";  "(app (app (const Nat.div) (lit ?l)) (lit ?r))" => { Op { op: u64_div,             lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws.push(       rewrite!("≡%";  "(app (app (const Nat.mod) (lit ?l)) (lit ?r))" => { Op { op: u64_mod,             lhs_nat_val : "?l".parse().unwrap(), rhs_nat_val : "?r".parse().unwrap() }}));
    rws
}

fn u64_pow(lhs: u64, rhs: u64) -> u64 {
    lhs.pow(u32::try_from(rhs).unwrap())
}

fn u64_div(lhs: u64, rhs: u64) -> u64 {
    lhs.checked_div(rhs).unwrap_or(0)
}

fn u64_mod(lhs: u64, rhs: u64) -> u64 {
    if rhs == 0 { lhs } else { lhs % rhs }
}