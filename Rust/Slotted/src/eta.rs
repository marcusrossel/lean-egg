use slotted_egraphs::*;
use crate::analysis::*;

pub fn eta_reduction_rw() -> LeanRewrite {
    Rewrite::new_if("≡η", "(λ $0 ?t (app ?f (bvar $0)))", "?f", |subst, _| {
        !subst["f"].slots().contains(&Slot::numeric(0))
    })
}

pub fn eta_expansion_rw() -> LeanRewrite {
    Rewrite::new("≡η+", "?e", "(λ $0 _ (app ?e (bvar $0)))")
}