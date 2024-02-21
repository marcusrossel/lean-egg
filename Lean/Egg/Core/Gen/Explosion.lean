import Egg.Core.Rewrites.Basic
import Egg.Lean
import Lean
open Lean Meta

namespace Egg

-- TODO:
#check abstractMVars               -- e -> λ xs, e
#check forallMetaTelescopeReducing -- λ xs, e -> e

private def Rewrite.explode (rw : Rewrite) : MetaM Rewrites := do
  match rw.validDirs with
  | .both     => return #[]
  | .forward  => return #[]
  | .backward => return #[]
  | .none     => return #[]
where
  backwardRws (rw : Rewrite) : MetaM Rewrites := do
    let unboundMVars := rw.lhsMVars.expr.subtract rw.rhsMVars.expr
    let mut current : Rewrites := #[rw]
    let mut next    : Rewrites := #[]
    for var in unboundMVars do
      for cur in current do
        for decl in (← getLCtx) do
          let cur' ← cur.fresh -- TODO: Adjust the source.
          -- if var.getType
          sorry
    return next

  -- Create and register an explosion rewrite from `side` to the other side.
  explosionRwFromSide (side : Side) : MetaM Rewrite := do
    let rw ← rw.fresh (src := .explosion rw.src 0)
    let targetMVars := match side with
      | .left  => rw.rhsMVars.expr.subtract rw.lhsMVars.expr
      | .right => rw.lhsMVars.expr.subtract rw.rhsMVars.expr
    let targetLMVars := match side with
      | .left  => rw.rhsMVars.lvl.subtract rw.lhsMVars.lvl
      | .right => rw.lhsMVars.lvl.subtract rw.rhsMVars.lvl
    return rw

def Rewrites.explode (rws : Rewrites) : MetaM Rewrites := do
  rws.foldlM (init := #[]) fun acc rw => return acc ++ (← rw.explode)
