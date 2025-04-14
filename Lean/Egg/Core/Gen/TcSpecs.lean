import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

namespace Egg

-- Important: This function expects the given rewrite to be fresh.
partial def genSpecialization
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

-- TODO: With type class instance erasure enabled, all type class instances become conditions, so we
--       should only need condition specialization.
private def genTcSpecializationsForRw
    (rw : Rewrite) (norm : Config.Normalization) (conditionSubgoals : Bool) : MetaM Rewrites := do
  let mut specs : Rewrites := #[]
  let missingOnLhs := rw.mvars.rhs.tcInsts.subtract rw.mvars.lhs.tcInsts
  let missingOnRhs := rw.mvars.lhs.tcInsts.subtract rw.mvars.rhs.tcInsts
  if let some fwd ← genDir .forward  missingOnLhs conditionSubgoals then specs := specs.push fwd
  if let some bwd ← genDir .backward missingOnRhs conditionSubgoals then specs := specs.push bwd
  if specs.isEmpty then if let some c ← genCondSpecOnly then specs := specs.push c
  return specs
where
  genDir (dir : Direction) (missing : MVarIdSet) (conditionSubgoals : Bool) :
      MetaM (Option Rewrite) := do
    unless !missing.isEmpty do return none
    let (freshRw, subst) ← rw.freshWithSubst (src := .tcSpec rw.src <| .dir dir)
    let freshMissing := missing.map subst.expr.get!
    let conds := freshRw.tcConditionMVars
    let (spec, _) ← genSpecialization freshRw (freshMissing.union conds) norm
    return if (← spec.validDirs conditionSubgoals).contains dir then spec else none
  genCondSpecOnly : MetaM (Option Rewrite) := do
    let freshRw ← rw.fresh (src := .tcSpec rw.src .cond)
    let conds := freshRw.tcConditionMVars
    let (spec, changed) ← genSpecialization freshRw conds norm
    return if changed then spec else none

def genTcSpecializations
    (targets : Rewrites) (norm : Config.Normalization) (conditionSubgoals : Bool) :
    MetaM Rewrites := do
  let mut result := #[]
  for rw in targets do result := result ++ (← genTcSpecializationsForRw rw norm conditionSubgoals)
  return result
