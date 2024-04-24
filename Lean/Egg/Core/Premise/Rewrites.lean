import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Ambient
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg

structure Rewrite extends Congr where
  proof    : Expr
  src      : Source
  conds    : Array Expr
  lhsMVars : MVars
  rhsMVars : MVars
  deriving Inhabited

namespace Rewrite

def isConditional (rw : Rewrite) : Bool :=
  !rw.conds.isEmpty

def validDirs (rw : Rewrite) : Directions :=
  let exprDirs := Directions.satisfyingSuperset rw.lhsMVars.expr rw.rhsMVars.expr
  let lvlDirs  := Directions.satisfyingSuperset rw.lhsMVars.lvl rw.rhsMVars.lvl
  exprDirs.meet lvlDirs

-- Returns the same rewrite but with its type and proof potentially flipped to match the given
-- direction.
def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with lhs := rw.rhs, rhs := rw.lhs, proof := ← rw.rel.mkSymm rw.proof }

def eqProof (rw : Rewrite) : MetaM Expr := do
  match rw.rel with
  | .eq  => return rw.proof
  | .iff => mkPropExt rw.proof

def freshWithSubst (rw : Rewrite) (src : Source := rw.src) : MetaM (Rewrite × MVars.Subst) := do
  let (lhsMVars, subst) ← rw.lhsMVars.fresh
  let (rhsMVars, subst) ← rw.rhsMVars.fresh (init := subst)
  let rw' := { rw with
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    src, lhsMVars, rhsMVars
  }
  return (rw', subst)

-- Returns the same rewrite but with all (expression and level) mvars replaced by fresh mvars. This
-- is used during proof reconstruction, as rewrites may be used multiple times but instantiated
-- differently. If we don't use fresh mvars, the mvars will already be assigned and new assignment
-- (via `isDefEq`) will fail.
def fresh (rw : Rewrite) (src : Source := rw.src) : MetaM Rewrite :=
  Prod.fst <$> rw.freshWithSubst src

def instantiateMVars (rw : Rewrite) : MetaM Rewrite :=
  return { rw with
    lhs      := ← Lean.instantiateMVars rw.lhs
    rhs      := ← Lean.instantiateMVars rw.rhs
    proof    := ← Lean.instantiateMVars rw.proof
    lhsMVars := ← rw.lhsMVars.removeAssigned
    rhsMVars := ← rw.rhsMVars.removeAssigned
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
