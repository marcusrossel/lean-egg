use slotted_egraphs::*;
use crate::analysis::*;

pub fn beta_reduction_rw() -> LeanRewrite {
    Rewrite::new("≡β", "(app (λ $0 ?t ?b) ?a)", "?b[(bvar $0) := ?a]")
}