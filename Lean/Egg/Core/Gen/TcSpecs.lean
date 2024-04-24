import Egg.Core.Premise.Rewrites
import Std.Tactic.Exact
import Lean
open Lean Meta

namespace Egg

private partial def genSpecialization
    (rw : Rewrite) (dir : Direction) (missing : MVarIdSet) (norm : Config.Normalization) :
    MetaM (Option Rewrite) := do
  let (rw, subst) ← rw.freshWithSubst (src := .tcSpec rw.src dir)
  let mut missing := missing.map subst.expr.fwd.find!
  let mut changed := true
  while changed do
    changed := false
    for var in missing do
      if let some inst ← instanceForType? (← var.getType) then
        var.assign inst
        missing := missing.erase var
        changed := true
  let rw ← rw.instantiateMVars
  return if rw.validDirs.contains dir then rw else none
where
  instanceForType? (type : Expr) : MetaM (Option Expr) := do
    if let some inst ← findLocalDeclWithType? type then
      return (Expr.fvar inst)
    else if let some inst ← optional (synthInstance type) then
      normalize inst norm
    else
      return none

private def genTcSpecializationsForRw (rw : Rewrite) (norm : Config.Normalization) :
    MetaM Rewrites := do
  let missingOnLhs := rw.rhsMVars.tc.subtract rw.lhsMVars.tc
  let missingOnRhs := rw.lhsMVars.tc.subtract rw.rhsMVars.tc
  let mut specs : Rewrites := #[]
  if !missingOnLhs.isEmpty then
    if let some spec ← genSpecialization rw .forward missingOnLhs norm then
    specs := specs.push spec
  if !missingOnRhs.isEmpty then
    if let some spec ← genSpecialization rw .backward missingOnRhs norm then
    specs := specs.push spec
  return specs

def genTcSpecializations (targets : Rewrites) (norm : Config.Normalization) : MetaM Rewrites :=
  targets.foldlM (init := #[]) fun acc rw =>
    return acc ++ (← genTcSpecializationsForRw rw norm)
