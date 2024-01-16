import Egg.Lean
open Lean

namespace Egg.Rewrite

inductive Source where
  | explicit (idx : Nat) (eqn? : Option Nat) (stx? : Option Syntax)
  | star (id : FVarId)
  deriving Inhabited

def Source.stx? : Source → Option Syntax
  | explicit _ _ stx => stx
  | star _           => none

def Source.description : Source → String
  | explicit idx none _       => s!"#{idx}"
  | explicit idx (some eqn) _ => s!"#{idx}/{eqn}"
  | star id                   => s!"*{id.uniqueIdx!}"

inductive Direction where
  | forward
  | backward
  | both

instance : ToString Direction where
  toString
    | .forward  => "forward"
    | .backward => "backward"
    | .both     => "both"

def Direction.for? (lhs rhs : Expr) (ignoreULvls : Bool) : MetaM (Option Direction) := do
  let lhsM ← Meta.getMVars lhs
  let rhsM ← Meta.getMVars rhs
  let mut lSubR := lhsM.all rhsM.contains
  let mut rSubL := rhsM.all lhsM.contains
  if !ignoreULvls then
    let lhsL := lhs.levelMVars
    let rhsL := rhs.levelMVars
    lSubR := lSubR && lhsL.all rhsL.contains
    rSubL := rSubL && rhsL.all lhsL.contains
  match lSubR, rSubL with
  | false, false => return none
  | false, true  => return some .forward
  | true,  false => return some .backward
  | true,  true  => return some .both

protected structure Candidate where
  lhs : Expr
  rhs : Expr
  src : Source

-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, cf.
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
def Candidate.from? (type : Expr) (src : Rewrite.Source) :
    MetaM (Option Rewrite.Candidate) := do
  let (_, _, body) ← Meta.forallMetaTelescopeReducing (← instantiateMVars type)
  let some (lhs, rhs) := body.eqOrIff? | return none
  return some { lhs, rhs, src }

abbrev Candidates := Array Rewrite.Candidate

end Rewrite

structure Rewrite extends Rewrite.Candidate where
  dir : Rewrite.Direction

abbrev Rewrites := Array Rewrite

def Rewrites.from! (cs : Rewrite.Candidates) (ignoreULvls : Bool) : MetaM Rewrites :=
  cs.mapM fun c => do
    if let some dir ← Rewrite.Direction.for? c.lhs c.rhs ignoreULvls
    then return { c with dir }
    else throwErrorAt? c.src.stx? "'egg' tactic (currently) disallows rewrite rules with loose mvars or level mvars"
