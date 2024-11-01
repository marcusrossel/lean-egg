use slotted_egraphs::*;
use crate::analysis::*;

pub fn level_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.push(Rewrite::new("≡maxS", "(max (succ ?a) (succ ?b))", "(succ (max ?b ?a))"));
    rws.push(Rewrite::new("≡maxS-rev", "(succ (max ?b ?a))", "(max (succ ?a) (succ ?b))"));
    rws.push(Rewrite::new("≡max↔", "(max ?a ?b)", "(max ?b ?a)"));
    rws.push(Rewrite::new("≡imax0", "(imax ?a 0)", "0"));
    rws.push(Rewrite::new("≡imaxS", "(imax ?a (succ ?b))", "(max ?a (succ ?b))"));
    rws
}