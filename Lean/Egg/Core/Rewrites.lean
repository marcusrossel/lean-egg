import Egg.Lean
open Lean Meta Elab

namespace Egg.Rewrite

inductive Source where
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  deriving Inhabited, BEq

def Source.description : Source → String
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"*{id.uniqueIdx!}"

inductive Direction where
  | forward
  | backward
  deriving Inhabited

def Direction.merge : Direction → Direction → Direction
  | .forward, .forward  | .backward, .backward => .forward
  | .forward, .backward | .backward, .forward  => .backward

inductive Directions where
  | forward
  | backward
  | both

instance : ToString Directions where
  toString
    | .forward  => "forward"
    | .backward => "backward"
    | .both     => "both"

-- TODO: Is this the right approach, or would it be better the store the type as a `∀` expression?
--
-- When constructed from a theorem `thm : ∀ xs, l = r`, the resulting rewrite has:
-- * `lhs := l`
-- * `rhs := r`
-- * `holes := xs`
-- * `proof := thm xs` - that is, the arguments are instantiated
structure _root_.Egg.Rewrite where private mk ::
  src   : Rewrite.Source
  lhs   : Expr
  rhs   : Expr
  holes : Array MVarId
  proof : Expr

def fresh (rw : Rewrite) : MetaM Rewrite := do
  let mut freshMVars : HashMap MVarId Expr := ∅
  let mut holes : Array MVarId := .mkEmpty rw.holes.size
  for hole in rw.holes do
    let fresh ← mkFreshExprMVar (← hole.getType)
    freshMVars := freshMVars.insert hole fresh
    holes := holes.push fresh.mvarId!
  let refreshMVars e := if e.isMVar then freshMVars.find? e.mvarId! else none
  let lhs   := rw.lhs.replace refreshMVars
  let rhs   := rw.rhs.replace refreshMVars
  let proof := rw.proof.replace refreshMVars
  return { rw with lhs, rhs, holes, proof }

def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with lhs := rw.rhs, rhs := rw.lhs, proof := ← Meta.mkEqSymm rw.proof }

def validDirs (rw : Rewrite) (ignoreULvls : Bool) : MetaM (Option Directions) := do
  let lhsM ← Meta.getMVars rw.lhs
  let rhsM ← Meta.getMVars rw.rhs
  let mut lSubR := lhsM.all rhsM.contains
  let mut rSubL := rhsM.all lhsM.contains
  if !ignoreULvls then
    let lhsL := rw.lhs.levelMVars
    let rhsL := rw.rhs.levelMVars
    lSubR := lSubR && lhsL.all rhsL.contains
    rSubL := rSubL && rhsL.all lhsL.contains
  match lSubR, rSubL with
  | false, false => return none
  | false, true  => return some .forward
  | true, false  => return some .backward
  | true, true   => return some .both

-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, cf.
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
def from? (proof : Expr) (type : Expr) (src : Source) : MetaM (Option Rewrite) := do
  let (args, _, type) ← Meta.forallMetaTelescopeReducing (← instantiateMVars type)
  let some (lhs, rhs) := type.eqOrIff? | return none
  let proof := mkAppN proof args
  return some { src, lhs, rhs, proof, holes := args.map (·.mvarId!) }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Rewrite.Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
