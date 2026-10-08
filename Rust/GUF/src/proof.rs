use std::rc::Rc;
use rs2::*;

// GUF annotates e-class ids with elements of a group, which we instantiate with proofs. That is,
// if `x` is an e-class id which represents the term `t`, then `(p, x)` represents the term `t'`
// where `p` is a proof of `t = t'`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum ProofObj {
    Refl,
    Sym(Proof),
    // `Trans(p, q)` first applies `q`, then `p` (cf. `Group::compose`).
    Trans(Proof, Proof),
    // Applies proofs to the children of a term (in the order of `LeanExpr::children`).
    Congr(Box<[Proof]>),
    // An application of the rewrite rule with the given name, which rewrites the term represented
    // by `lhs` to the term represented by `rhs`.
    Rule { name: Rc<str>, lhs: PId, rhs: PId },
}

// Note: This needs to be a new type, as Rust's orphan rule forbids implementing `Group` for `Rc`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Proof(pub Rc<ProofObj>);

// A proof-annotated e-class id.
pub type PId = (Proof, Id);

impl Proof {

    pub fn is_refl(&self) -> bool {
        matches!(*self.0, ProofObj::Refl)
    }

    pub fn congr(children: Vec<Proof>) -> Proof {
        if children.iter().all(Proof::is_refl) {
            Proof::identity()
        } else {
            Proof(Rc::new(ProofObj::Congr(children.into())))
        }
    }

    pub fn rule(name: &str, lhs: PId, rhs: PId) -> Proof {
        Proof(Rc::new(ProofObj::Rule { name: name.into(), lhs, rhs }))
    }
}

impl Group for Proof {

    fn identity() -> Self {
        Proof(Rc::new(ProofObj::Refl))
    }

    fn compose(l: &Self, r: &Self) -> Self {
        if l.is_refl() {
            r.clone()
        } else if r.is_refl() {
            l.clone()
        } else {
            Proof(Rc::new(ProofObj::Trans(l.clone(), r.clone())))
        }
    }

    fn inverse(&self) -> Self {
        match &*self.0 {
            ProofObj::Refl   => self.clone(),
            ProofObj::Sym(p) => p.clone(),
            _                => Proof(Rc::new(ProofObj::Sym(self.clone())))
        }
    }
}

// The proof-annotated e-class id used for the (ignored) children of e-nodes in patterns.
pub fn nil() -> PId {
    (Proof::identity(), Id(0))
}
