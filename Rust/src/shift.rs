/*
use slotted_egraphs::*;
use crate::lean_expr::*;
use crate::analysis::*;

struct BVarShift {
    dir:      Var,
    offset:   Var,
    cutoff:   Var,
    bvar_idx: Var
}

impl Applier<LeanExpr, LeanAnalysis> for BVarShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, shift_class: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // Determine if we have a self-loop for the shift-node. If so, the shift-node must be in an e-class 
        // where some node contains no loose bvars. Thus, all other loose bvars which appear under the given
        // e-class must be redundant. Thus, we don't propagate the shift at all, because otherwise we run into
        // endless shifting.
        egraph.rebuild();
        let bvar = LeanExpr::BVar(subst[self.bvar_idx]);
        let bvar_class = egraph.lookup(bvar).unwrap();
        if egraph.find(shift_class) == egraph.find(bvar_class) { return vec![] };
        
        let dir_is_up = egraph[subst[self.dir]].data.dir_val.unwrap();
        let offset    = egraph[subst[self.offset]].data.nat_val.unwrap();
        let cutoff    = egraph[subst[self.cutoff]].data.nat_val.unwrap();
        let bvar_idx  = egraph[subst[self.bvar_idx]].data.nat_val.unwrap();

        let new_idx = if bvar_idx < cutoff {
            bvar_idx
        } else if dir_is_up {
            bvar_idx + offset
        } else if offset <= bvar_idx {
            bvar_idx - offset
        } else {
            // If `offset > bvar_idx`, this shift was "not intended", so we just don't do it. 
            return vec![]
        };
        let new = format!("(bvar {})", new_idx).parse().unwrap();
        
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &new, subst, rule);
        vec![id]
    }
}

struct AppShift {
    dir:    Var,
    offset: Var,
    cutoff: Var,
    fun:    Var,
    arg:    Var
}

impl Applier<LeanExpr, LeanAnalysis> for AppShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, shift_class: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // Determine if we have a self-loop for the shift-node. If so, the shift-node must be in an e-class 
        // where some node contains no loose bvars. Thus, all other loose bvars which appear under the given
        // e-class must be redundant. Thus, we don't propagate the shift at all, because otherwise we run into
        // endless shifting.
        egraph.rebuild();
        let app = LeanExpr::App([subst[self.fun], subst[self.arg]]);
        let app_class = egraph.lookup(app).unwrap();
        if egraph.find(shift_class) == egraph.find(app_class) { return vec![] };
        
        let fun_bvars = &egraph[subst[self.fun]].data.loose_bvars;
        let arg_bvars = &egraph[subst[self.arg]].data.loose_bvars;
        let cutoff    = &egraph[subst[self.cutoff]].data.nat_val.unwrap();

        let shifted_fun: PatternAst<LeanExpr> = if fun_bvars.iter().all(|b| b < cutoff) { 
            format!("{}", self.fun).parse().unwrap()
        } else { 
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.fun).parse().unwrap()
        };

        let shifted_arg: PatternAst<LeanExpr> = if arg_bvars.iter().all(|b| b < cutoff) { 
            format!("{}", self.arg).parse().unwrap()
        } else { 
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.arg).parse().unwrap()
        };

        let shifted_app = format!("(app {} {})", shifted_fun, shifted_arg).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &shifted_app, subst, rule);
        vec![id]
    }
}

struct BinderShift {
    binder:   String,
    dir:      Var,
    offset:   Var,
    cutoff:   Var,
    domain:   Var,
    body:     Var
}

impl Applier<LeanExpr, LeanAnalysis> for BinderShift {

    fn apply_one(&self, egraph: &mut LeanEGraph, shift_class: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // Determine if we have a self-loop for the shift-node. If so, the shift-node must be in an e-class 
        // where some node contains no loose bvars. Thus, all other loose bvars which appear under the given
        // e-class must be redundant. Thus, we don't propagate the shift at all, because otherwise we run into
        // endless shifting.
        egraph.rebuild();
        let binder = if self.binder == "λ" {
            LeanExpr::Lam([subst[self.domain], subst[self.body]])
        } else if self.binder == "∀" {
            LeanExpr::Forall([subst[self.domain], subst[self.body]])
        } else {
            panic!("Unknown binder {}", self.binder)
        };
        
        let binder_class = egraph.lookup(binder).unwrap();
        if egraph.find(shift_class) == egraph.find(binder_class) { return vec![] };
        
        let domain_bvars = &egraph[subst[self.domain]].data.loose_bvars;
        let body_bvars   = &egraph[subst[self.body]].data.loose_bvars;
        let cutoff       = &egraph[subst[self.cutoff]].data.nat_val.unwrap();

        let shifted_domain: PatternAst<LeanExpr> = if domain_bvars.iter().all(|b| b < cutoff) { 
            format!("{}", self.domain).parse().unwrap()
        } else { 
            format!("(↑ {} {} {} {})", self.dir, self.offset, self.cutoff, self.domain).parse().unwrap()
        };

        let shifted_body: PatternAst<LeanExpr> = if body_bvars.iter().all(|b| b <= cutoff) {
            format!("{}", self.body).parse().unwrap()
        } else { 
            format!("(↑ {} {} {} {})", self.dir, self.offset, cutoff + 1, self.body).parse().unwrap()
        };

        let shifted_binder = format!("({} {} {})", self.binder, shifted_domain, shifted_body).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &shifted_binder, subst, rule);
        vec![id]
    }
}

// We don't introduce shifting rules for constructors which can't contain bvars in the first place.
// Instead, we make sure to never introduce shifting nodes over such constructors, á la
// https://pldi23.sigplan.org/details/egraphs-2023-papers/12/Optimizing-Beta-Reduction-in-E-Graphs
pub fn shift_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(rewrite!("↑bvar"; "(↑ ?d ?o ?c (bvar ?b))"   => { BVarShift   { dir: "?d".parse().unwrap(), offset: "?o".parse().unwrap(), cutoff: "?c".parse().unwrap(), bvar_idx: "?b".parse().unwrap() }}));
    rws.push(rewrite!("↑app";  "(↑ ?d ?o ?c (app ?a ?b))" => { AppShift    { dir: "?d".parse().unwrap(), offset: "?o".parse().unwrap(), cutoff: "?c".parse().unwrap(), fun: "?a".parse().unwrap(), arg: "?b".parse().unwrap() }}));
    rws.push(rewrite!("↑λ";    "(↑ ?d ?o ?c (λ ?a ?b))"   => { BinderShift { binder: "λ".to_string(), dir: "?d".parse().unwrap(), offset: "?o".parse().unwrap(), cutoff: "?c".parse().unwrap(), domain: "?a".parse().unwrap(), body: "?b".parse().unwrap() }}));
    rws.push(rewrite!("↑∀";    "(↑ ?d ?o ?c (∀ ?a ?b))"   => { BinderShift { binder: "∀".to_string(), dir: "?d".parse().unwrap(), offset: "?o".parse().unwrap(), cutoff: "?c".parse().unwrap(), domain: "?a".parse().unwrap(), body: "?b".parse().unwrap() }}));
    // TODO: Do we need shifting over the `proof` constructor, or can we ignore that for now as we disallow type-level rewrites anyway?
    rws
}
*/