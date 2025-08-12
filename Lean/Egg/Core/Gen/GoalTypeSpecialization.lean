import Egg.Core.Rewrite.Rule
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

private def specializeForTargets (rw : Rewrite) (goalUnif rwUnif : Expr) (subgoals : Bool) :
    MetaM (Option Rewrite) := do
  let mut (spec, subst) ← rw.freshWithSubst
  unless ← isDefEq goalUnif (subst.apply rwUnif) do return none
  spec ← spec.instantiateMVars
  unless ← spec.isValid subgoals do return none
  return spec

private def specialize (rule : Rewrite.Rule) (goal : Congr) (subgoals : Bool) : MetaM Rewrite.Rules := do
  -- Computes the unification targets.
  let goalTargets ← goal.unificationTargets
  let rwTargets   ← rule.rw.unificationTargets
  -- (Potentially) generates a rewrite for each pair of unification targets.
  let mut result := ∅
  let mut idx := 0
  for goalTarget in goalTargets do
    for rwTarget in rwTargets do
      let some spec ← specializeForTargets rule.rw goalTarget rwTarget subgoals | continue
      result := result.insert <| spec.with (.goalTypeSpec rule.src idx) rule.dir
      idx := idx + 1
  return result

def genGoalTypeSpecializations (rules : Rewrite.Rules) (goal : Congr) (subgoals : Bool) :
    MetaM Rewrite.Rules := do
  let mut result := ∅
  for rule in rules.entries do
    if ← rule.rw.isValid subgoals then continue
    let specs ← specialize rule goal subgoals
    result := result ∪ specs
  return result
