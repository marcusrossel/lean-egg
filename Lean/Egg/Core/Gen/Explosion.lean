import Egg.Core.Rewrites.Basic
import Egg.Core.Encode.Rewrites
import Egg.Lean
import Lean
open Lean Meta

namespace Egg

-- An index of which expression and level mvars should be replaced by explosion vars during
-- encoding. Note that all rewrites (should) have disjoint mvars which is why we don't need to
-- distinguish which rewrite should have its mvars replaced.
private abbrev ExplosionM := StateT MVars MetaM

private def ExplosionM.withEmptyVars (m : ExplosionM α) :=
  StateT.run m {}

private def ExplosionM.register (vars : MVars) : ExplosionM Unit :=
  modify (·.merge vars)

private def Rewrite.explode (rw : Rewrite) : ExplosionM Rewrites := do
  match rw.dirs with
  | .both     => return #[]
  | .forward  => return #[← explosionRwFromSide .right]
  | .backward => return #[← explosionRwFromSide .left]
  | .none     => return #[← explosionRwFromSide .right, ← explosionRwFromSide .left]
where
  -- Create and register an explosion rewrite from `side` to the other side.
  explosionRwFromSide (side : Side) : ExplosionM Rewrite := do
    let rw ← rw.fresh (src := .explosion <| .rw rw.src side) (dirs := dirForSide side)
    let targetMVars := match side with
      | .left  => rw.rhsMVars.expr.subtract rw.lhsMVars.expr
      | .right => rw.lhsMVars.expr.subtract rw.rhsMVars.expr
    let targetLMVars := match side with
      | .left  => rw.rhsMVars.lvl.subtract rw.lhsMVars.lvl
      | .right => rw.lhsMVars.lvl.subtract rw.rhsMVars.lvl
    ExplosionM.register { expr := targetMVars, lvl := targetLMVars }
    return rw

  dirForSide : Side → Directions
    | .left => .forward
    | .right => .backward

def Rewrites.explode (rws : Rewrites) : MetaM (Rewrites × MVars) :=
  ExplosionM.withEmptyVars do
    rws.foldlM (init := #[]) fun acc rw => return acc ++ (← rw.explode)

def explosionExprSubsts : MetaM Rewrites.Encoded := do
  let mut rws : Rewrites.Encoded := #[]
  let lctx ← getLCtx
  for decl in lctx, idx in [:lctx.decls.size] do
    rws := rws.push {
      name := (Source.explosion <| .exprSubst idx).description
      lhs  := "ε",
      rhs  := s!"(fvar {decl.fvarId.uniqueIdx!})"
      dirs := .forward
    }
  return rws


-- set_option trace.egg true in
-- theorem t {α : Type _} (a : α) : ULift.down (ULift.up a) = a := by
--   egg [List.append_assoc]


-- all possible universe parameters must be present in the local context and goal type
-- (note when using `example` instead of `theorem` these params show up as lmvars)
--
-- so when we traverse rewrites for additional levels we can only hope to find additional constant
-- levels or combinations (using max/imax/succ...) of given params and constants
