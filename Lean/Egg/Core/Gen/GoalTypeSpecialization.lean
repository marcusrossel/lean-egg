import Egg.Core.Rewrites
import Lean
open Lean Meta

namespace Egg

/-
For goal type specialization, we consider the following shapes of goals and rewrites:

(1) . = .       where . is not a proposition
(2) (_ = _) ~ . where . is a proposition (necessarily)
(3) . ~ (_ = _) where . is a proposition (necessarily)

First note that a goal or rewrite can have shapes (2) and (3) at the same time.
In that case, we need to try multiple specializations.

From these 3 shapes, we get the following combinations for what should be unified with eachother:

⊢   Rw  Unify
1   1   (EQ_TYPE ⊢)       with (EQ_TYPE Rw)
1   2   (EQ_TYPE ⊢)       with (EQ_TYPE (LHS Rw))
1   3   (EQ_TYPE ⊢)       with (EQ_TYPE (RHS Rw))
2   1   (EQ_TYPE (LHS ⊢)) with (EQ_TYPE Rw)
2   2   (EQ_TYPE (LHS ⊢)) with (EQ_TYPE (LHS Rw))
2   3   (EQ_TYPE (LHS ⊢)) with (EQ_TYPE (RHS Rw))
3   1   (EQ_TYPE (RHS ⊢)) with (EQ_TYPE Rw)
3   2   (EQ_TYPE (RHS ⊢)) with (EQ_TYPE (LHS Rw))
3   3   (EQ_TYPE (RHS ⊢)) with (EQ_TYPE (RHS Rw))

That is, the goal's unification target is independent of the rewrite's unification target and vice
versa. It can be determined completely from the shape.
-/
private def Congr.unificationTargets (cgr : Congr) : MetaM (List Expr) := do
  let cgrType ← cgr.type
  -- Shape 1:
  if cgrType.isProp then
  -- Shapes 2 & 3:
    let mut targets := []
    if let some (target, _, _) := cgr.lhs.eq? then targets := target :: targets
    if let some (target, _, _) := cgr.rhs.eq? then targets := target :: targets
    return targets
  else
    return [cgrType]

private def specializeForTargets
    (rw : Rewrite) (rwDirs : Directions) (goalUnif rwUnif : Expr) (subgoals : Bool) (idx : Nat) :
    MetaM (Option Rewrite) := do
  let mut (spec, subst) ← rw.freshWithSubst (src := .goalTypeSpec rw.src idx)
  unless ← isDefEq goalUnif (subst.apply rwUnif) do return none
  spec ← spec.instantiateMVars
  -- We set the specialization's directions to not include those already covered by `rw`. If that
  -- means that the specialization does not have any direction, then we discard it.
  let newDirs := (spec.validDirs subgoals).without rwDirs
  if newDirs.isNone then return none
  return spec.fixDirs newDirs

private def specialize (rw : Rewrite) (goal : Congr) (subgoals : Bool) :
    MetaM (Array Rewrite) := do
  -- If the given rewrite is already valid in both directions, then we don't generate any
  -- specializations for it.
  let rwDirs := rw.validDirs subgoals
  if rwDirs.isBoth then return #[]
  -- Computes the unification targets.
  let goalTargets ← goal.unificationTargets
  let rwTargets   ← rw.unificationTargets
  -- (Potentially) generates a rewrite for each pair of unification targets.
  let mut result := #[]
  let mut idx := 0
  for goalTarget in goalTargets do
    for rwTarget in rwTargets do
      let some spec ← specializeForTargets rw rwDirs goalTarget rwTarget subgoals idx | continue
      let spec' ← spec.pruneSynthesizableConditions
      result := result.push spec'
      idx := idx + 1
  return result

def genGoalTypeSpecializations (targets : Rewrites) (goal : Congr) (subgoals : Bool) :
    MetaM Rewrites := do
  let mut result := #[]
  for rw in targets do
    let specs ← specialize rw goal subgoals
    result := result ++ specs
  return result
