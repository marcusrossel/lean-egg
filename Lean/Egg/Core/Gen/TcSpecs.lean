import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

namespace Egg

private partial def genSpecialization
    (rw : Rewrite) (dirs : Directions) (missing : MVarIdSet) (norm : Config.Normalization) :
    MetaM (Rewrite × Bool) := do
  let (rw, subst) ← rw.freshWithSubst (src := .tcSpec rw.src dirs)
  let mut missing := missing.map subst.expr.fwd.find!
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

private def genTcSpecializationsForRw (rw : Rewrite) (norm : Config.Normalization) (eager : Bool) :
    MetaM Rewrites := do
  let mut specs : Rewrites := #[]
  let missingOnLhs := rw.mvars.rhs.tc.subtract rw.mvars.lhs.tc
  let missingOnRhs := rw.mvars.lhs.tc.subtract rw.mvars.rhs.tc
  if let some fwd ← genDir .forward missingOnLhs then specs := specs.push fwd
  if let some bwd ← genDir .backward missingOnRhs then specs := specs.push bwd
  if eager then
    let (spec, changed) ← genSpecialization rw .both (rw.mvars.lhs.tc.merge rw.mvars.rhs.tc) norm
    if changed then specs := specs.push spec
  return specs
where
  genDir (dir : Direction) (missing : MVarIdSet) : MetaM (Option Rewrite) := do
    unless !missing.isEmpty do return none
    let (spec, _) ← genSpecialization rw dir missing norm
    unless spec.validDirs.contains dir do return none
    return spec

def genTcSpecializations (targets : Rewrites) (norm : Config.Normalization) (eager : Bool) :
    MetaM Rewrites :=
  targets.foldlM (init := #[]) fun acc rw =>
    return acc ++ (← genTcSpecializationsForRw rw norm eager)
