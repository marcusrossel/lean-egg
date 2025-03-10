use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;

struct BVarSubst {
    from_idx: Var,
    to:       Var,
    bvar_idx: Var
}

impl Applier<LeanExpr, LeanAnalysis> for BVarSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let from_idx = egraph[subst[self.from_idx]].data.nat_val.unwrap();
        let bvar_idx = egraph[subst[self.bvar_idx]].data.nat_val.unwrap();

        let new: PatternAst<LeanExpr> = if from_idx == bvar_idx { 
            format!("{}", self.to).parse().unwrap()
        } else { 
            format!("(bvar {})", bvar_idx).parse().unwrap()
        };
        
        let (id, did_union) = egraph.union_instantiations(ast.unwrap(), &new, subst, rule);
        if did_union { vec![id] } else { vec![] }
    }
}

struct BasicSubst {
    ctor:     String,
    from_idx: Var,
    to:       Var,
    left:     Var,
    right:    Var
}

impl Applier<LeanExpr, LeanAnalysis> for BasicSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let from_idx    = egraph[subst[self.from_idx]].data.nat_val.unwrap();
        let left_bvars  = &egraph[subst[self.left]].data.loose_bvars;
        let right_bvars = &egraph[subst[self.right]].data.loose_bvars;

        let new_left: PatternAst<LeanExpr> = if left_bvars.contains(&from_idx) { 
            format!("(↦ {} {} {})", self.from_idx, self.to, self.left).parse().unwrap()
        } else { 
            format!("{}", self.left).parse().unwrap()
        };

        let new_right: PatternAst<LeanExpr> = if right_bvars.contains(&from_idx) { 
            format!("(↦ {} {} {})", self.from_idx, self.to, self.right).parse().unwrap()
        } else { 
            format!("{}", self.right).parse().unwrap()
        };
        
        let new_expr = format!("({} {} {})", self.ctor, new_left, new_right).parse().unwrap();
        let (id, did_union) = egraph.union_instantiations(ast.unwrap(), &new_expr, subst, rule);
        if did_union { vec![id] } else { vec![] }
    }
}

struct BinderSubst {
    binder:   String,
    from_idx: Var,
    to:       Var,
    domain:   Var,
    body:     Var
}

impl Applier<LeanExpr, LeanAnalysis> for BinderSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let from_idx     = egraph[subst[self.from_idx]].data.nat_val.unwrap();
        let to_bvars     = &egraph[subst[self.to]].data.loose_bvars;
        let domain_bvars = &egraph[subst[self.domain]].data.loose_bvars;
        let body_bvars   = &egraph[subst[self.body]].data.loose_bvars;

        let new_domain: PatternAst<LeanExpr> = if domain_bvars.contains(&from_idx) { 
            format!("(↦ {} {} {})", self.from_idx, self.to, self.domain).parse().unwrap()
        } else { 
            format!("{}", self.domain).parse().unwrap()
        };

        let new_body: PatternAst<LeanExpr> = if body_bvars.contains(&(from_idx + 1)) {
            let to_shifted: PatternAst<LeanExpr> = if to_bvars.is_empty() {
                format!("{}", self.to).parse().unwrap()
            } else {
                format!("(↑ + 1 0 {})", self.to).parse().unwrap()
            };
            format!("(↦ {} {} {})", from_idx + 1, to_shifted, self.body).parse().unwrap()
        } else { 
            format!("{}", self.body).parse().unwrap()
        };

        let new_binder = format!("({} {} {})", self.binder, new_domain, new_body).parse().unwrap();
        let (id, did_union) = egraph.union_instantiations(ast.unwrap(), &new_binder, subst, rule);
        if did_union { vec![id] } else { vec![] }
    }
}

// We try to reduce the number of introduced substitution rules á la
// https://pldi23.sigplan.org/details/egraphs-2023-papers/12/Optimizing-Beta-Reduction-in-E-Graphs
// TODO: Is this ok when using intersection semantics?
pub fn subst_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(rewrite!("↦bvar";  "(↦ ?f ?t (bvar ?b))"     => { BVarSubst   { from_idx : "?f".parse().unwrap(), to : "?t".parse().unwrap(), bvar_idx : "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦app";   "(↦ ?f ?t (app ?a ?b))"   => { BasicSubst  { ctor: "app".to_string(), from_idx: "?f".parse().unwrap(), to: "?t".parse().unwrap(), left:   "?a".parse().unwrap(), right: "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦=";     "(↦ ?f ?t (= ?a ?b))"     => { BasicSubst  { ctor: "=".to_string(),   from_idx: "?f".parse().unwrap(), to: "?t".parse().unwrap(), left:   "?a".parse().unwrap(), right: "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦λ";     "(↦ ?f ?t (λ ?a ?b))"     => { BinderSubst { binder: "λ".to_string(), from_idx: "?f".parse().unwrap(), to: "?t".parse().unwrap(), domain: "?a".parse().unwrap(), body:  "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦∀";     "(↦ ?f ?t (∀ ?a ?b))"     => { BinderSubst { binder: "∀".to_string(), from_idx: "?f".parse().unwrap(), to: "?t".parse().unwrap(), domain: "?a".parse().unwrap(), body:  "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦fvar";  "(↦ ?f ?t (fvar ?x))"     => "(fvar ?x)"));
    rws.push(rewrite!("↦mvar";  "(↦ ?f ?t (mvar ?x))"     => "(mvar ?x)"));
    rws.push(rewrite!("↦sort";  "(↦ ?f ?t (sort ?x))"     => "(sort ?x)"));
    rws.push(rewrite!("↦const"; "(↦ ?f ?t (const ?x ?l))" => "(const ?x ?l)"));
    rws.push(rewrite!("↦lit";   "(↦ ?f ?t (lit ?x))"      => "(lit ?x)"));
    // TODO: We don't propagate substitutions over erased terms at the moment.
    rws.push(rewrite!("↦proof"; "(↦ ?f ?t (proof ?x))"    => "(proof ?x)"));
    rws.push(rewrite!("↦inst";  "(↦ ?f ?t (inst ?x))"     => "(inst ?x)"));
    rws.push(rewrite!("↦_";     "(↦ ?f ?t _)"             => "_"));
    // Note: We don't handle the propagation of substitutions over facts, as a substitution should 
    //       never even be applied to a fact.
    rws
}
