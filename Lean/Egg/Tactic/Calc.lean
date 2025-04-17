import Egg.Tactic.Basic
open Lean Meta Elab Tactic
open Egg.Config.Modifier (egg_cfg_mod)

namespace Egg

private def appendPremises :
    (TSyntax `egg_premises) → (TSyntax `egg_premises) → TacticM (TSyntax `egg_premises)
  | `(egg_premises|$[$ps₁]?), `(egg_premises|$[$ps₂]?) =>
    match ps₁, ps₂ with
    | ps, none | none, ps => `(egg_premises|$[$ps]?)
    | some ps₁, some ps₂ => do
      match ps₁, ps₂ with
      | `(egg_premise_list| [$rws₁,*]), `(egg_premise_list| [$rws₂,*]) =>
        let rws := rws₁.getElems ++ rws₂
        `(egg_premises| [$rws,*])
      | _, _ => throwUnsupportedSyntax
  | _, _ => throwUnsupportedSyntax

namespace Calc

syntax egg_calc_step := ppIndent(colGe term (&" with " egg_cfg_mod egg_premises)? (egg_guides)?)

structure Step where
  mod    : TSyntax ``egg_cfg_mod
  prems  : TSyntax `egg_premises
  guides : Option (TSyntax `egg_guides)
  deriving Inhabited

structure Step.Raw extends Step where
  goal : Term
  deriving Inhabited

structure Step.Elab extends Step where
  lhs : Expr
  rhs : Expr
  stx : Syntax

def Step.Raw.equiv? (s : Step.Raw) : Option (Term × Term) := do
  match s.goal with
  | `($lhs = $rhs) => (lhs, rhs)
  | `($lhs ↔ $rhs) => (lhs, rhs)
  | _              => none

def parseRawStep : (TSyntax ``egg_calc_step) → TacticM Step.Raw
  | `(egg_calc_step| $goal $[with $mod $prems]? $[$guides]?) => do
    let mod ← mod.getDM `(egg_cfg_mod|)
    let prems ← prems.getDM `(egg_premises|)
    return { goal, mod, prems, guides }
  | _ => throwUnsupportedSyntax

syntax egg_calc_steps :=
  ppLine withPosition(egg_calc_step) withPosition((ppLine linebreak egg_calc_step)*)

structure RawSteps where
  head : Step.Raw
  tail : Array Step.Raw
  deriving Inhabited

def parseRawSteps : (TSyntax ``egg_calc_steps) → TacticM RawSteps
  | `(egg_calc_steps| $head $[
      $tail]*) => return { head := ← parseRawStep head, tail := ← tail.mapM parseRawStep }
  | _ => throwUnsupportedSyntax

syntax &"egg " ident* &" calc " egg_premises egg_calc_steps : tactic

def eval
    (baskets : Array Ident) (prems : TSyntax `egg_premises) (steps : TSyntax ``egg_calc_steps) :
    TacticM Unit := do
  withMainContext do
    let rawSteps ← parseRawSteps steps
    let some goal ← Congr.from? (← getMainTarget)
      | throwError "'egg calc' expects a proof goal of the form '_ = _' or '_ ↔ _'"
    let headStep? ← processHead rawSteps.head goal.lhs
    let steps ← elabSteps goal <| headStep?.elim rawSteps.tail (#[·] ++ rawSteps.tail)
    let mut subgoals := []
    let mut proof ← mkEqRefl goal.lhs
    for step in steps do
      let stepMVar ← mkFreshExprMVar (← goal.rel.relate step.lhs step.rhs)
      proof ← goal.rel.mkTrans proof stepMVar
      try
        let sub ← evalTacticAt (← stepToEgg step.toStep) stepMVar.mvarId!
        subgoals := subgoals ++ sub
      catch err =>
        throwErrorAt step.stx err.toMessageData
    (← getMainGoal).assignIfDefeq' proof
    appendGoals (← dedupSubgoals subgoals)
where
  stepToEgg (step : Step) : TacticM (TSyntax `tactic) := do
    let allPrems ← appendPremises step.prems prems
    `(tactic| egg $[$baskets]* $step.mod:egg_cfg_mod $allPrems $[$step.guides]?)
  dedupSubgoals (subgoals : List MVarId) : MetaM (List MVarId) := do
    let mut result := []
    for subgoal in subgoals do
      -- Note: When unifying two mvars, the first is assigned.
      let dup ← result.findM? fun m => isDefEq (.mvar subgoal) (.mvar m)
      if dup.isNone then result := subgoal :: result
    return result
  processHead (step : Step.Raw) (goalLhs : Expr) : TacticM (Option Step.Raw) := do
    if step.equiv?.isSome then
      return step
    else if step.goal.isWildcard then
      return none
    else
      let headLhs ← elabTerm step.goal none
      unless ← isDefEq goalLhs headLhs do
        throwErrorAt step.goal "first step of 'egg calc' block does not match RHS of the proof goal"
      return none
  elabSteps (goal : Congr) (steps : Array Step.Raw) : TacticM <| Array Step.Elab := do
    let mut lastRhs := goal.lhs
    let mut result := #[]
    for step in steps, idx in [:steps.size] do
      let isLast := idx = steps.size - 1
      let some (lhs, rhs) := step.equiv?
        | throwErrorAt step.goal "'egg calc' expects steps to be of the form '_ = _' or '_ ↔ _'"
      let lhs ← do
        if lhs.isWildcard then
          pure lastRhs
        else
          let l ← elabTerm lhs none
          unless ← isDefEq l lastRhs do
            throwErrorAt lhs "LHS is not definitionally equal to RHS of the previous step"
          pure l
      let rhs ← do
        if isLast then
          if rhs.isWildcard then
            pure goal.rhs
          else
            let r ← elabTerm rhs none
            unless ← isDefEq r goal.rhs do
              throwErrorAt rhs "final step of 'egg calc' block does not match RHS of the proof goal"
            pure r
        else
          elabTerm rhs none
      result := result.push { step with lhs, rhs, stx := step.goal }
      lastRhs := rhs
    return result

elab "egg " baskets:ident* " calc " prems:egg_premises steps:egg_calc_steps : tactic =>
  eval baskets prems steps
