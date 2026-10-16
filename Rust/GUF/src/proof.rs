use std::rc::Rc;
use rs2::*;
use crate::LeanExpr;

// GUF annotates e-class ids with elements of a group, which we instantiate with proofs. That is,
// if `x` is an e-class id which represents the term `t`, then `(p, x)` represents the term `t'`
// where `p` is a proof of `t = t'`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum ProofObj {
    Refl,
    Sym(Proof), // maps q to q⁻¹

    // `Trans(p, q)` first applies `q`, then `p` (cf. `Group::compose`).
    Trans(Proof, Proof),

    // Applies proofs to the children of a term (in the order of `LeanExpr::children`).
    Congr(SymbolId, Box<[Proof]>),

    // An application of the rewrite rule with the given id in the e-graph's `RuleTable`. The proof
    // rewrites an instance of the rule's `lhs` to the corresponding instance of its `rhs`.
    Rule(RuleId),
}

// An index into a `RuleTable`.
pub type RuleId = usize;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SymbolId(u8);

impl SymbolId {
    pub fn from_enode(e: &LeanExpr) -> SymbolId {
        use LeanExpr::*;
        SymbolId(match e {
            Nat(_) => 0,
            Str(_) => 1,
            UVar(_) => 2,
            Param(_) => 3,
            Succ(_) => 4,
            Max(_) => 5,
            IMax(_) => 6,
            BVar(_) => 7,
            FVar(_) => 8,
            MVar(_) => 9,
            Sort(_) => 10,
            Const(_) => 11,
            App(_) => 12,
            Lam(_) => 13,
            Forall(_) => 14,
            Lit(_) => 15,
            Proof(_) => 16,
            Inst(_) => 17,
            Eq(_) => 18,
            Fact(_) => 19,
            Subst(_) => 20,
            Shift(_) => 21,
            Fun(_) => 22,
            Shaped(_) => 23,
            Unknown => 24,
        })
    }

    pub fn build(self, children: Box<[PId]>) -> LeanExpr {
        use LeanExpr::*;
        let c = |i: usize| children[i].clone();
        match self.0 {
            0 => Nat(unreachable!()),
            1 => Str(unreachable!()),
            2 => UVar(c(0)),
            3 => Param(c(0)),
            4 => Succ(c(0)),
            5 => Max([c(0), c(1)]),
            6 => IMax([c(0), c(1)]),
            7 => BVar(c(0)),
            8 => FVar(c(0)),
            9 => MVar(c(0)),
            10 => Sort(c(0)),
            11 => Const(children),
            12 => App([c(0), c(1)]),
            13 => Lam([c(0), c(1)]),
            14 => Forall([c(0), c(1)]),
            15 => Lit(c(0)),
            16 => Proof(c(0)),
            17 => Inst(c(0)),
            18 => Eq([c(0), c(1)]),
            19 => Fact(c(0)),
            20 => Subst([c(0), c(1), c(2)]),
            21 => Shift([c(0), c(1), c(2), c(3)]),
            22 => Fun([c(0), c(1)]),
            23 => Shaped([c(0), c(1)]),
            24 => Unknown,
            _ => unreachable!(),
        }
    }
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

    pub fn congr(sym_id: SymbolId, children: Vec<Proof>) -> Proof {
        if children.iter().all(Proof::is_refl) {
            Proof::identity()
        } else {
            Proof(Rc::new(ProofObj::Congr(sym_id, children.into())))
        }
    }

    pub fn rule(rule: RuleId) -> Proof {
        Proof(Rc::new(ProofObj::Rule(rule)))
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
