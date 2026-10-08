use rs2::PVar;
use crate::analysis::*;
use crate::egraph::*;
use crate::proof::*;
use crate::rewrite::*;
use crate::util::*;
use std::ops::*;

struct ToSucc {
    nat_val: PVar,
    shapes:  bool
}

impl ToSucc {

    fn rewrite(shapes: bool) -> LeanRewrite {
        rewrite!("≡→S"; "(lit ?n)" => { ToSucc { nat_val : PVar::from("?n"), shapes }})
    }
}

impl Applier for ToSucc {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        // This applier matches against "lit ?n", which means that `?n` might be a string.
        if let Some(nat_val) = egraph.data(&subst[&self.nat_val]).nat_val {
            if !(nat_val > 0) { return }

            let res =
                if self.shapes { format!("(app (◇ (→ * *) (const Nat.succ)) (◇ * (lit {})))", nat_val - 1) }
                else           { format!("(app (const Nat.succ) (lit {}))",                   nat_val - 1) };

            union_instantiation(egraph, from, &pat(&res), subst, rule);
        }
    }
}

struct OfSucc {
    nat_val: PVar
}

impl OfSucc {

    fn rewrite(shapes: bool) -> LeanRewrite {
        if shapes { rewrite!("≡S→"; "(app (◇ (→ * *) (const Nat.succ)) (◇ * (lit ?n)))" => { OfSucc { nat_val : PVar::from("?n") }}) }
        else      { rewrite!("≡S→"; "(app (const Nat.succ) (lit ?n))"                   => { OfSucc { nat_val : PVar::from("?n") }}) }
    }
}

impl Applier for OfSucc {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        // This applier is only used in a context where we know that `nat_val` is a `LeanExpr::Nat` and thus has a `nat_val`.
        let nat_val = egraph.data(&subst[&self.nat_val]).nat_val.unwrap();
        let res = format!("(lit {})", nat_val + 1);
        union_instantiation(egraph, from, &pat(&res), subst, rule);
    }
}

struct Op {
    lhs_nat_val: PVar,
    rhs_nat_val: PVar,
    op: fn(u64, u64) -> u64
}

impl Op {

    fn rewrite(rule: &str, op_name: &str, op: fn(u64, u64) -> u64, shapes: bool) -> LeanRewrite {
        let pattern =
            if shapes { format!("(app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const Nat.{})) (◇ * (lit ?l)))) (◇ * (lit ?r)))", op_name) }
            else      { format!("(app (app (const Nat.{}) (lit ?l)) (lit ?r))",                                           op_name) };

        let applier = Op { op, lhs_nat_val : PVar::from("?l"), rhs_nat_val : PVar::from("?r") };
        mk_rewrite(rule, pat(&pattern), applier)
    }
}

impl Applier for Op {

    fn apply_one(&self, egraph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        // This applier is only used in a context where we know that `nat_val` is a `LeanExpr::Nat` and thus has a `nat_val`.
        let lhs = egraph.data(&subst[&self.lhs_nat_val]).nat_val.unwrap();
        let rhs = egraph.data(&subst[&self.rhs_nat_val]).nat_val.unwrap();

        let val = (self.op)(lhs, rhs);
        let res = format!("(lit {})", val);
        union_instantiation(egraph, from, &pat(&res), subst, rule);
    }
}

// The supported internalizations can be found at:
// https://github.com/leanprover/lean4/blob/1e74c6a348416677987cd71a59a451db0aef9e26/src/kernel/type_checker.cpp#L1138
pub fn nat_lit_rws(shapes: bool) -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("≡0"; "(lit 0)" <=> "(const Nat.zero)"));
    rws.push(ToSucc::rewrite(shapes));
    rws.push(OfSucc::rewrite(shapes));
    rws.push(Op::rewrite("≡+", "add", u64::add,            shapes));
    rws.push(Op::rewrite("≡-", "sub", u64::saturating_sub, shapes));
    rws.push(Op::rewrite("≡*", "mul", u64::mul,            shapes));
    rws.push(Op::rewrite("≡^", "pow", u64_pow,             shapes));
    rws.push(Op::rewrite("≡/", "div", u64_div,             shapes));
    rws.push(Op::rewrite("≡%", "mod", u64_mod,             shapes));
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
