use egg::*;
use crate::analysis::*;

pub fn level_rws() -> Vec<LeanRewrite> {
    let mut rws = vec![];
    rws.append(&mut rewrite!("≡maxS";  "(max (succ ?a) (succ ?b))" <=> "(succ (max ?b ?a))"));
    rws.push(       rewrite!("≡max↔";  "(max ?a ?b)" => "(max ?b ?a)"));
    rws.push(       rewrite!("≡imax0"; "(imax ?a 0)" => "0"));
    rws.push(       rewrite!("≡imaxS"; "(imax ?a (succ ?b))" => "(max ?a (succ ?b))"));
    rws
}