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

structure _root_.Egg.Rewrite.Condition where
  kind  : Kind
  mvar  : MVarId
  type  : Expr

inductive Result where
  | none
  | synthesized
  | unsynthesizable
  | some (cond : Condition)

def from? (mvar : MVarId) (lhs : MVars) : MetaM Result := do
  let some kind ← kind? | return .none
  -- Note: It seems `inferType` does not instantiate mvars.
  let type ← instantiateMVars (← inferType <| .mvar mvar)
  -- This is a small optimization. If a type class can already be synthesized, we do it immediately
  -- and don't generate a condition to be synthesized during eqsat.
  match ← trySynthesizeTcInst type kind with
  | .undef => return .some { kind, mvar, type }
  | .true  => return .synthesized
  | .false => return .unsynthesizable
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
  trySynthesizeTcInst (type : Expr) : Kind → MetaM LBool
  | .proof  => return .undef
  | .tcInst => do
    if type.hasMVar then return .undef
    let some inst ← synthInstance? type | return .false
    unless ← isDefEq (.mvar mvar) inst do
      throwError "Internal error in 'Egg.Rewrite.Condition.from?.synthesizeTcInst?'"
    return .true

def fresh (cond : Condition) (init : MVars.Subst) : MetaM (Condition × MVars.Subst) := do
  let (_, subst) ← (← MVars.collect <| .mvar cond.mvar).fresh init
  let fresh := { cond with
    mvar := subst.expr[cond.mvar]!
    type := subst.apply cond.type
  }
  return (fresh, subst)
