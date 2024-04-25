import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Ambient
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg

structure Rewrite.MVars where
  lhs   : MVars
  rhs   : MVars
  conds : Array MVars
  deriving Inhabited

-- Note: We don't create `Rewrite`s directly, but use `Premise.from` instead.
structure Rewrite extends Congr where
  proof : Expr
  src   : Source
  conds : Array Expr
  mvars : Rewrite.MVars
  deriving Inhabited

namespace Rewrite

def isConditional (rw : Rewrite) : Bool :=
  !rw.conds.isEmpty

def validDirs (rw : Rewrite) : Directions :=
  let exprDirs := Directions.satisfyingSuperset rw.mvars.lhs.expr rw.mvars.rhs.expr
  let lvlDirs  := Directions.satisfyingSuperset rw.mvars.lhs.lvl rw.mvars.rhs.lvl
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
  let (mLhs,   subst) ← rw.mvars.lhs.fresh
  let (mRhs,   subst) ← rw.mvars.rhs.fresh (init := subst)
  let (mConds, subst) ← MVars.fresh' rw.mvars.conds (init := subst)
  let rw' := { rw with
    src
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    conds := rw.conds.map subst.apply
    mvars := { lhs := mLhs, rhs := mRhs, conds := mConds }
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
    lhs         := ← Lean.instantiateMVars rw.lhs
    rhs         := ← Lean.instantiateMVars rw.rhs
    proof       := ← Lean.instantiateMVars rw.proof
    mvars.lhs   := ← rw.mvars.lhs.removeAssigned
    mvars.rhs   := ← rw.mvars.rhs.removeAssigned
    mvars.conds := ← rw.mvars.conds.mapM (·.removeAssigned)
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
