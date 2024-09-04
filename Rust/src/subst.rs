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
        
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &new, subst, rule);
        vec![id]
    }
}

struct AppSubst {
    from_idx: Var,
    to:       Var,
    fun:      Var,
    arg:      Var
}

impl Applier<LeanExpr, LeanAnalysis> for AppSubst {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let from_idx  = egraph[subst[self.from_idx]].data.nat_val.unwrap();
        let fun_bvars = &egraph[subst[self.fun]].data.loose_bvars;
        let arg_bvars = &egraph[subst[self.arg]].data.loose_bvars;

        let new_fun: PatternAst<LeanExpr> = if fun_bvars.contains(&from_idx) { 
            format!("(↦ {} {} {})", self.from_idx, self.to, self.fun).parse().unwrap()
        } else { 
            format!("{}", self.fun).parse().unwrap()
        };

        let new_arg: PatternAst<LeanExpr> = if arg_bvars.contains(&from_idx) { 
            format!("(↦ {} {} {})", self.from_idx, self.to, self.arg).parse().unwrap()
        } else { 
            format!("{}", self.arg).parse().unwrap()
        };
        
        let new_app = format!("(app {} {})", new_fun, new_arg).parse().unwrap();
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &new_app, subst, rule);
        vec![id]
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
        let (id, _) = egraph.union_instantiations(ast.unwrap(), &new_binder, subst, rule);
        vec![id]
    }
}

// We don't introduce substitution rules for constructors which can't contain bvars in the first place.
// Instead, we make sure to never introduce substitution nodes over such constructors, á la
// https://pldi23.sigplan.org/details/egraphs-2023-papers/12/Optimizing-Beta-Reduction-in-E-Graphs
pub fn subst_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(rewrite!("↦bvar"; "(↦ ?f ?t (bvar ?b))"   => { BVarSubst   { from_idx : "?f".parse().unwrap(), to : "?t".parse().unwrap(), bvar_idx : "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦app";  "(↦ ?f ?t (app ?a ?b))" => { AppSubst    { from_idx : "?f".parse().unwrap(), to : "?t".parse().unwrap(), fun : "?a".parse().unwrap(), arg : "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦λ";    "(↦ ?f ?t (λ ?a ?b))"   => { BinderSubst { binder: "λ".to_string(), from_idx : "?f".parse().unwrap(), to : "?t".parse().unwrap(), domain : "?a".parse().unwrap(), body : "?b".parse().unwrap() }}));
    rws.push(rewrite!("↦∀";    "(↦ ?f ?t (∀ ?a ?b))"   => { BinderSubst { binder: "∀".to_string(), from_idx : "?f".parse().unwrap(), to : "?t".parse().unwrap(), domain : "?a".parse().unwrap(), body : "?b".parse().unwrap() }}));
    // TODO: Do we need substitution over the `proof` constructor, or can we ignore that for now as we disallow type-level rewrites anyway?
    rws
}