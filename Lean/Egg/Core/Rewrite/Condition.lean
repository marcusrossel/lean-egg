import Egg.Core.MVars.Subst
import Egg.Core.MVars.Collect
open Lean Meta

namespace Egg.Rewrite

protected structure MVars where
  lhs : MVars
  rhs : MVars
  deriving Inhabited

namespace Condition

inductive Kind where
  | proof
  | tcInst
  deriving BEq

def Kind.isProof : Kind → Bool
  | proof  => true
  | tcInst => false

def Kind.isTcInst : Kind → Bool
  | proof  => false
  | tcInst => true

-- TODO: Remove this when tc spec is removed.
def Kind.forType? (ty : Expr) : MetaM (Option Kind) := do
  -- Since type classes can also be propositions, we do the type class check first.
  if (← Meta.isClass? ty).isSome then
    return some .tcInst
  else if ← Meta.isProp ty then
    return some .proof
  else
    return none

structure _root_.Egg.Rewrite.Condition where
  kind  : Kind
  mvar  : MVarId
  type  : Expr

inductive Result where
  | none
  | synthesized
  | some (cond : Condition)

def from? (mvar : MVarId) (lhs : MVars) : MetaM Result := do
  let some kind ← kind? | return .none
  -- Note: It seems `inferType` does not instantiate mvars.
  let type ← instantiateMVars (← inferType <| .mvar mvar)
  -- This is a small optimization. If a type class can already be synthesized, we do it immediately
  -- and don't generate a condition to be synthesized during eqsat.
  if ← trySynthesizeTcInst type kind
  then return .synthesized
  else return .some { kind, mvar, type }
where
  -- If the mvar appears in the LHS, then it's a condition only if it's a nested instance or proof.
  -- If it does not appear in the LHS, it's a condition immediately if it's an instance or proof.
  kind? : MetaM <| Option Kind := do
    if let some ps := lhs.expr[mvar]? then
      if ps.contains .isTcInst && ps.contains .inTcInstTerm then
        return some .tcInst
      else if ps.contains .isProof && ps.contains .inProofTerm then
        return some .proof
    else if ← isTCInstance (.mvar mvar) then
      return some .tcInst
    else if ← isProof (.mvar mvar) then
      return some .proof
    return none
  trySynthesizeTcInst (type : Expr) : Kind → MetaM Bool
  | .proof  => return false
  | .tcInst => do
    if type.hasMVar then return false
    let some inst ← synthInstance? type | return false
    unless ← isDefEq (.mvar mvar) inst do
      throwError "Internal error in 'Egg.Rewrite.Condition.from?.synthesizeTcInst?'"
    return true

-- If a condition's mvar is assigned, then the condition is redundant, and we return `none`.
nonrec def instantiateMVars (cond : Condition) : MetaM (Option Condition) := do
  if ← cond.mvar.isAssigned
  then return none
  else return some { cond with type := ← instantiateMVars cond.type }

def fresh (cond : Condition) (init : MVars.Subst) : MetaM (Condition × MVars.Subst) := do
  let (_, subst) ← (← MVars.collect <| .mvar cond.mvar).fresh init
  let fresh := { cond with
    mvar := subst.expr[cond.mvar]!
    type := subst.apply cond.type
  }
  return (fresh, subst)
