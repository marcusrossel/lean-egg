import Egg.Core.Rewrites.Basic
import Egg.Lean
import Lean
open Lean Meta

namespace Egg

-- An index of which expression and level mvars should be replaced by explosion vars during
-- encoding. Note that all rewrites (should) have disjoint mvars which is why we don't need to
-- distinguish which rewrite should have its mvars replaced.
abbrev ExplosionVars := Rewrite.MVars

private abbrev ExplosionM := StateT ExplosionVars MetaM

private def ExplosionM.withEmptyVars (m : ExplosionM α) :=
  StateT.run m {}

private def ExplosionM.register (vars : Rewrite.MVars) : ExplosionM Unit :=
  modify (·.merge vars)

private def Rewrite.explode (rw : Rewrite) : ExplosionM Rewrites := do
  match rw.validDirs with
  | .both     => return #[]
  | .forward  => return #[← explosionRwFromSide .right]
  | .backward => return #[← explosionRwFromSide .left]
  | .none     => return #[← explosionRwFromSide .right, ← explosionRwFromSide .left]
where
  -- Create and register an explosion rewrite from `side` to the other side.
  explosionRwFromSide (side : Side) : ExplosionM Rewrite := do
    let rw ← rw.fresh (src := .explosion <| .rw rw.src side)
    let targetMVars := match side with
      | .left  => rw.rhsMVars.expr.subtract rw.lhsMVars.expr
      | .right => rw.lhsMVars.expr.subtract rw.rhsMVars.expr
    let targetLMVars := match side with
      | .left  => rw.rhsMVars.lvl.subtract rw.lhsMVars.lvl
      | .right => rw.lhsMVars.lvl.subtract rw.rhsMVars.lvl
    ExplosionM.register { expr := targetMVars, lvl := targetLMVars }
    return rw

def Rewrites.explode (rws : Rewrites) : MetaM (Rewrites × ExplosionVars) := do
  ExplosionM.withEmptyVars do
    rws.foldlM (init := #[]) fun acc rw => return acc ++ (← rw.explode)
