import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

namespace Egg

def Rewrite.Condition.typeClassInstanceMVar? (cond : Condition) : MetaM (Option MVarId) := do
  if cond.expr.isMVar && (← isClass? cond.type).isSome
  then return cond.expr.mvarId!
  else return none

private def Rewrite.tcConditionMVars (rw : Rewrite) : MetaM MVarIdSet :=
  rw.conds.foldlM (init := ∅) fun cs c => do
    if let some m ← c.typeClassInstanceMVar?
    then return cs.insert m
    else return cs

-- Important: This function expects the given rewrite to be fresh.
private partial def genSpecialization
    (rw : Rewrite) (missing : MVarIdSet) (norm : Config.Normalization) :
    MetaM (Rewrite × Bool) := do
  let mut missing := missing
  let mut lastIterChanged := true
  let mut everChanged := false
  while lastIterChanged do
    lastIterChanged := false
    for var in missing do
      if let some inst ← instanceForType? (← var.getType) then
        unless ← isDefEq (.mvar var) inst do
          throwError "egg: internal error in 'Egg.genSpecialization'"
        missing := missing.erase var
        lastIterChanged := true
        everChanged := true
  let rw ← rw.instantiateMVars
  return (rw, everChanged)
where
  instanceForType? (type : Expr) : MetaM (Option Expr) := do
    if let some inst ← findLocalDeclWithType? type then
      return (Expr.fvar inst)
    else if let some inst ← optional (synthInstance type) then
      normalize inst norm
    else
      return none

private def genTcSpecializationsForRw
    (rw : Rewrite) (norm : Config.Normalization) (cfg : Config.Erasure) : MetaM Rewrites := do
  let mut specs : Rewrites := #[]
  let missingOnLhs := rw.mvars.rhs.tcInsts.subtract rw.mvars.lhs.tcInsts
  let missingOnRhs := rw.mvars.lhs.tcInsts.subtract rw.mvars.rhs.tcInsts
  if let some fwd ← genDir .forward  missingOnLhs then specs := specs.push fwd
  if let some bwd ← genDir .backward missingOnRhs then specs := specs.push bwd
  if specs.isEmpty then if let some c ← genCondSpecOnly then specs := specs.push c
  return specs
where
  genDir (dir : Direction) (missing : MVarIdSet) : MetaM (Option Rewrite) := do
    unless !missing.isEmpty do return none
    let (freshRw, subst) ← rw.freshWithSubst (src := .tcSpec rw.src <| .dir dir)
    let freshMissing := missing.map subst.expr.get!
    let conds ← freshRw.tcConditionMVars
    let (spec, _) ← genSpecialization freshRw (freshMissing.union conds) norm
    return if (spec.validDirs cfg).contains dir then spec else none
  genCondSpecOnly : MetaM (Option Rewrite) := do
    let freshRw ← rw.fresh (src := .tcSpec rw.src .cond)
    let conds ← freshRw.tcConditionMVars
    let (spec, changed) ← genSpecialization freshRw conds norm
    return if changed then spec else none

private def genGoalTypeSpecialization
    (rw : Rewrite) (goalType : Expr) (norm : Config.Normalization) : MetaM (Option Rewrite) := do
  let mut rw ← rw.fresh (src := .tcSpec rw.src .goalType)
  unless ← isDefEq (← inferType rw.lhs) goalType <&&> isDefEq (← inferType rw.rhs) goalType do
    return none
  rw ← rw.instantiateMVars
  let missing := rw.mvars.lhs.tcInsts.union rw.mvars.rhs.tcInsts
  let conds ← rw.tcConditionMVars
  let (spec, changed) ← genSpecialization rw (missing.union conds) norm
  return if changed then spec else none

-- Goal type specialization is only run if the given `goalType?` is not `none`.
def genTcSpecializations
    (targets : Rewrites) (norm : Config.Normalization) (cfg : Config.Erasure)
    (goalType? : Option Expr) : MetaM Rewrites := do
  let mut result := #[]
  for rw in targets do
    result := result ++ (← genTcSpecializationsForRw rw norm cfg)
  if let some goalType := goalType? then
    for rw in targets do
      if let some spec ← genGoalTypeSpecialization rw goalType norm then
        result := result.push spec
  return result
