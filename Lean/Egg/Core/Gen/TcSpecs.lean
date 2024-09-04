import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

namespace Egg

-- Important: This function expects the given rewrite to be fresh.
private partial def genSpecialization
    (rw : Rewrite) (missing : MVarIdSet) (norm : Config.Normalization) : MetaM (Rewrite × Bool) := do
  let mut missing := missing
  let mut lastIterChanged := true
  let mut everChanged := false
  while lastIterChanged do
    lastIterChanged := false
    for var in missing do
      if let some inst ← instanceForType? (← var.getType) then
        var.assign inst
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
    (rw : Rewrite) (norm : Config.Normalization) : MetaM Rewrites := do
  let mut specs : Rewrites := #[]
  let missingOnLhs := rw.mvars.rhs.tc.subtract rw.mvars.lhs.tc
  let missingOnRhs := rw.mvars.lhs.tc.subtract rw.mvars.rhs.tc
  if let some fwd ← genDir .forward  missingOnLhs then specs := specs.push fwd
  if let some bwd ← genDir .backward missingOnRhs then specs := specs.push bwd
  return specs
where
  genDir (dir : Direction) (missing : MVarIdSet) : MetaM (Option Rewrite) := do
    unless !missing.isEmpty do return none
    let (freshRw, subst) ← rw.freshWithSubst (src := .tcSpec rw.src <| .dir dir)
    let freshMissing := missing.map subst.expr.fwd.get!
    let (spec, _) ← genSpecialization freshRw freshMissing norm
    return if spec.validDirs.contains dir then spec else none

private def genGoalTypeSpecialization
    (rw : Rewrite) (goalType : Expr) (norm : Config.Normalization) : MetaM (Option Rewrite) := do
  let mut rw ← rw.fresh (src := .tcSpec rw.src .goalType)
  unless ← isDefEq (← inferType rw.lhs) goalType <&&> isDefEq (← inferType rw.rhs) goalType do
    return none
  rw ← rw.instantiateMVars
  let missing := rw.mvars.lhs.tc.merge rw.mvars.rhs.tc
  let (spec, changed) ← genSpecialization rw missing norm
  return if changed then spec else none

def genTcSpecializations
    (targets : Rewrites) (norm : Config.Normalization) (goalType? : Option Expr) :
    MetaM Rewrites := do
  let mut result := #[]
  for rw in targets do
    result := result ++ (← genTcSpecializationsForRw rw norm)
  if let some goalType := goalType? then
    for rw in targets do
      if let some spec ← genGoalTypeSpecialization rw goalType norm then
        result := result.push spec
  return result
