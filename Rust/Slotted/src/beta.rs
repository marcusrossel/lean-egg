use slotted_egraphs::*;
use crate::analysis::*;

pub fn beta_reduction_rws(small_step: bool) -> Vec<LeanRewrite> {
    if small_step {
        let mut rws = vec![];
        rws.push(Rewrite::new("≡β", "(app (λ $0 ?t ?b) ?a)", "(↦ $0 ?a ?b)"));
        rws.append(&mut subst_rws());
        rws
    } else {
        vec![Rewrite::new("≡β", "(app (λ $0 ?t ?b) ?a)", "?b[(bvar $0) := ?a]")]
    }
}

fn subst_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(Rewrite::new("↦bvar", "(↦ $x ?z (bvar $x))",    "?z"));
    rws.push(Rewrite::new("↦app",  "(↦ $x ?z (app ?a ?b))",  "(app (↦ $x ?z ?a) (↦ $x ?z ?b))"));
    rws.push(Rewrite::new("↦λ",    "(↦ $x ?z (λ $y ?t ?b))", "(λ $y (↦ $x ?z ?t) (↦ $x ?z ?b))"));
    rws.push(Rewrite::new("↦∀",    "(↦ $x ?z (∀ $y ?t ?b))", "(∀ $y (↦ $x ?z ?t) (↦ $x ?z ?b))"));
    rws.push(Rewrite::new_if("↦|", "(↦ $x ?z ?e)", "?e", |subst, _| { 
        !subst["e"].slots().contains(&Slot::named("x"))
    }));
    // TODO: We don't propagate substitutions over erased terms at the moment.
    rws
}