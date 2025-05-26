import Egg.Core.Gen.TcSpecs
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
private partial def genGoalTypeSpecializations
    (rw : Rewrite) (goal : Congr) (norm : Config.Normalization) (conditionSubgoals : Bool) :
    MetaM (Array Rewrite) := do
  let goalTargets ← unificationTargets goal
  let rwTargets   ← unificationTargets rw.toCongr
  let mut result := #[]
  let mut idx := 0
  for goalTarget in goalTargets do
    for rwTarget in rwTargets do
      let some spec ← core idx rw goalTarget rwTarget | continue
      result := result.push spec
      idx := idx + 1
  return result
where
  core (idx : Nat) (target : Rewrite) (goalUnif rwUnif : Expr) : MetaM (Option Rewrite) := do
    let mut (rw, subst) ← target.freshWithSubst (src := .tcSpec target.src (.goalType idx))
    unless ← isDefEq goalUnif (subst.apply rwUnif) do return none
    rw ← rw.instantiateMVars
    let missing := rw.mvars.lhs.tcInsts |>.union rw.mvars.rhs.tcInsts |>.union rw.tcConditionMVars
    let (spec, changed) ← genSpecialization rw missing norm
    panic! "Unimplemented"
    /-
    if changed && (target.validDirs conditionSubgoals != spec.validDirs conditionSubgoals) then
      return spec
    else
      return none
    -/

  unificationTargets (cgr : Congr) : MetaM (List Expr) := do
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

def genGoalTcSpecializations
    (targets : Rewrites) (norm : Config.Normalization) (conditionSubgoals : Bool) (goal : Congr) :
    MetaM Rewrites := do
  let mut result := #[]
  for rw in targets do result := result ++ (← genGoalTypeSpecializations rw goal norm conditionSubgoals)
  return result
