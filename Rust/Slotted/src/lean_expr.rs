use slotted_egraphs::*;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum LeanExpr {
    // Primitives:
    Nat(u64),
    Str(String),

    // Encoding of universe levels:
    // Note, we don't encode `zero` explicitly, and use `Nat(0)` for that instead.
    UVar(AppliedId),            // (Nat)
    Param(AppliedId),           // (Str)
    Succ(AppliedId),            // (<level>)
    Max(AppliedId, AppliedId),  // (<level>, <level>)
    IMax(AppliedId, AppliedId), // (<level>, <level>)
    
    // Encoding of expressions:
    BVar(Slot),                         // (<var>)
    FVar(AppliedId),                    // (Nat)
    MVar(AppliedId),                    // (Nat)
    Sort(AppliedId),                    // (<level>)
    Const(Box<[AppliedId]>),            // (Str, <level>*)
    App(AppliedId, AppliedId),          // (<expr>, <expr>)
    Lam(Slot, AppliedId, AppliedId),    // (<var>, <expr>, <expr>)
    Forall(Slot, AppliedId, AppliedId), // (<var>, <expr>, <expr>)
    Lit(AppliedId),                     // (Nat | Str)

    // Construct for proof erasure:
    Proof(AppliedId),

    // Construct for small-step substitution:
    Subst(Slot, AppliedId, AppliedId),  // (<var>, <expr>, <expr>)

    // Constructs for shape annotations:
    // Note, we don't encode the shape of non-function types explicitly and use `Str("*")`) for that 
    // instead.
    Fun(AppliedId, AppliedId),          // (<shape>, <shape>)
    Shaped(AppliedId, AppliedId),       // (<shape>, <expr>)
}

impl Language for LeanExpr {

    fn all_slot_occurences_mut(&mut self) -> Vec<&mut Slot> { 
        let mut out = Vec::new();
        match self {
            LeanExpr::Lam(x, e1, e2) | LeanExpr::Forall(x, e1, e2) | LeanExpr::Subst(x, e1, e2) => {
                out.push(x);
                out.extend(e1.slots_mut());
                out.extend(e2.slots_mut());
            },
            LeanExpr::BVar(x) => {
                out.push(x);
            },
            LeanExpr::App(e1, e2) => {
                out.extend(e1.slots_mut());
                out.extend(e2.slots_mut());
            },
            LeanExpr::Proof(e) | LeanExpr::Shaped(_, e) => {
                out.extend(e.slots_mut());
            },
            _ => {}
        }
        out
    }

    fn public_slot_occurences_mut(&mut self) -> Vec<&mut Slot> { 
        let mut out = Vec::new();
        match self {
            LeanExpr::Lam(x, t, b) | LeanExpr::Forall(x, t, b) => {
                out.extend(t.slots_mut());
                out.extend(b.slots_mut().into_iter().filter(|y| *y != x));
            },
            LeanExpr::BVar(x) => {
                out.push(x);
            },
            LeanExpr::App(e1, e2) => {
                out.extend(e1.slots_mut());
                out.extend(e2.slots_mut());
            },
            LeanExpr::Proof(e) | LeanExpr::Shaped(_, e) => {
                out.extend(e.slots_mut());
            },
            LeanExpr::Subst(x, e1, e2) => {
                out.push(x);
                out.extend(e1.slots_mut());
                out.extend(e2.slots_mut());
            }
            _ => {}
        }
        out
    }

    fn applied_id_occurences_mut(&mut self) -> Vec<&mut AppliedId> { 
        match self {
            LeanExpr::UVar(i) | LeanExpr::Param(i) | LeanExpr::Succ(i) | 
            LeanExpr::FVar(i) | LeanExpr::MVar(i) | LeanExpr::Sort(i) | 
            LeanExpr::Lit(i) | LeanExpr::Proof(i) => vec![i],  

            LeanExpr::Max(i1, i2) | LeanExpr::IMax(i1, i2) | LeanExpr::App(i1, i2) | 
            LeanExpr::Lam(_, i1, i2) | LeanExpr::Forall(_, i1, i2) | LeanExpr::Subst(_, i1, i2) | 
            LeanExpr::Fun(i1, i2) | LeanExpr::Shaped(i1, i2) => vec![i1, i2],  
            
            LeanExpr::Const(is) => {
                let mut v = Vec::new();
                for i in &mut **is { v.push(i); }
                v
            },  
            
            _ => vec![],
        }
    }
    
    fn to_op(&self) -> (String, Vec<Child>) {
        match self.clone() {
            LeanExpr::Nat(n)             => (format!("{}", n), vec![]),
            LeanExpr::Str(s)             => (format!("\"{}\"", s), vec![]),
            LeanExpr::UVar(c)            => ("uvar".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Param(c)           => ("param".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Succ(c)            => ("succ".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Max(c1, c2)        => ("max".to_string(), vec![Child::AppliedId(c1), Child::AppliedId(c2)]),
            LeanExpr::IMax(c1, c2)       => ("imax".to_string(), vec![Child::AppliedId(c1), Child::AppliedId(c2)]),
            LeanExpr::BVar(c)            => ("bvar".to_string(), vec![Child::Slot(c)]), 
            LeanExpr::FVar(c)            => ("fvar".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::MVar(c)            => ("mvar".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Sort(c)            => ("sort".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::App(c1, c2)        => ("app".to_string(), vec![Child::AppliedId(c1), Child::AppliedId(c2)]),
            LeanExpr::Lam(c1, c2, c3)    => ("λ".to_string(), vec![Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]),
            LeanExpr::Forall(c1, c2, c3) => ("∀".to_string(), vec![Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]),
            LeanExpr::Lit(c)             => ("lit".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Proof(c)           => ("proof".to_string(), vec![Child::AppliedId(c)]),
            LeanExpr::Subst(c1, c2, c3)  => ("↦".to_string(), vec![Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]),
            LeanExpr::Fun(c1, c2)        => ("→".to_string(), vec![Child::AppliedId(c1), Child::AppliedId(c2)]),
            LeanExpr::Shaped(c1, c2)     => ("◇".to_string(), vec![Child::AppliedId(c1), Child::AppliedId(c2)]),
            LeanExpr::Const(cs)          => {
                let mut is = Vec::new();
                for c in cs.iter() { is.push(Child::AppliedId(c.clone())); }
                ("const".to_string(), is)
            }
        }
    }
    
    fn from_op(op: &str, children: Vec<Child>) -> Option<Self> {
        match (op, &*children) {
            ("uvar",  [Child::AppliedId(c)])                                         => Some(LeanExpr::UVar(c.clone())),            
            ("param", [Child::AppliedId(c)])                                         => Some(LeanExpr::Param(c.clone())),           
            ("succ",  [Child::AppliedId(c)])                                         => Some(LeanExpr::Succ(c.clone())),            
            ("max",   [Child::AppliedId(c1), Child::AppliedId(c2)])                  => Some(LeanExpr::Max(c1.clone(), c2.clone())),        
            ("imax",  [Child::AppliedId(c1), Child::AppliedId(c2)])                  => Some(LeanExpr::IMax(c1.clone(), c2.clone())),       
            ("bvar",  [Child::Slot(c)])                                              => Some(LeanExpr::BVar(*c)),            
            ("fvar",  [Child::AppliedId(c)])                                         => Some(LeanExpr::FVar(c.clone())),            
            ("mvar",  [Child::AppliedId(c)])                                         => Some(LeanExpr::MVar(c.clone())),            
            ("sort",  [Child::AppliedId(c)])                                         => Some(LeanExpr::Sort(c.clone())),            
            ("app",   [Child::AppliedId(c1), Child::AppliedId(c2)])                  => Some(LeanExpr::App(c1.clone(), c2.clone())),        
            ("λ",     [Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]) => Some(LeanExpr::Lam(*c1, c2.clone(), c3.clone())),    
            ("∀",     [Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]) => Some(LeanExpr::Forall(*c1, c2.clone(), c3.clone())), 
            ("lit",   [Child::AppliedId(c)])                                         => Some(LeanExpr::Lit(c.clone())),             
            ("proof", [Child::AppliedId(c)])                                         => Some(LeanExpr::Proof(c.clone())),     
            ("↦",     [Child::Slot(c1), Child::AppliedId(c2), Child::AppliedId(c3)]) => Some(LeanExpr::Subst(*c1, c2.clone(), c3.clone())),     
            ("→",     [Child::AppliedId(c1), Child::AppliedId(c2)])                  => Some(LeanExpr::Fun(c1.clone(), c2.clone())),     
            ("◇",     [Child::AppliedId(c1), Child::AppliedId(c2)])                  => Some(LeanExpr::Shaped(c1.clone(), c2.clone())),     
            ("const", cs) => {
                let mut is = vec![];
                for c in cs.iter() {
                    match c {
                        Child::Slot(_)      => return None,
                        Child::AppliedId(i) => { is.push(i.clone()); }
                    }
                }
                Some(LeanExpr::Const(is.into_boxed_slice()))
            },
            (op, []) => {
                if let Ok(n) = op.parse::<u64>() {
                    Some(LeanExpr::Nat(n))
                } else if op.starts_with("\"") && op.ends_with("\"") {
                    let s = op.strip_prefix("\"").unwrap().strip_suffix("\"").unwrap().to_string();
                    Some(LeanExpr::Str(s))
                } else {
                    None
                }
            },
            (op, cs) => panic!("Failed to parse ctor {} with {} children", op, cs.len())
        }
    }
}