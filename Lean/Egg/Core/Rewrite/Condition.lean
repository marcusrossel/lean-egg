import Egg.Core.MVars.Collect
open Lean

namespace Egg.Rewrite

protected structure MVars where
  lhs : MVars
  rhs : MVars
  deriving Inhabited

namespace Condition

inductive Kind where
  | proof
  | tcInst

def Kind.isProof : Kind → Bool
  | proof  => true
  | tcInst => false

def Kind.isTcInst : Kind → Bool
  | proof  => false
  | tcInst => true

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
  -- TODO: Change (and rename) `expr` to be an `MVarId`, as it should never be anything else.
  expr  : Expr
  type  : Expr
  -- These are the mvars of `type`.
  mvars : MVars

def from? (mvar : MVarId) (lhs : MVars) : MetaM <| Option Condition := do
  let some kind ← kind? | return none
  let type ← Meta.inferType (.mvar mvar)
  return some { kind, expr := (.mvar mvar), type, mvars := ← MVars.collect type }
where
  -- If the mvar appears in the LHS, then it's a condition only if it's a nested instance or proof.
  -- If it does not appear in the LHS, it's a condition immediately if it's an instance or proof.
  kind? : MetaM <| Option Kind := do
    if let some ps := lhs.expr[mvar]? then
      if ps.contains .isTcInst && ps.contains .inTcInstTerm then
        return some .tcInst
      else if ps.contains .isProof && ps.contains .inProofTerm then
        return some .proof
    else if ← Meta.isTCInstance (.mvar mvar) then
      return some .tcInst
    else if ← Meta.isProof (.mvar mvar) then
      return some .proof
    return none

-- Conditions can become proven during type class specialization. We still need to keep these
-- conditions in order to use their `expr` during proof reconstruction. Proven conditions are not
-- encoded and thus transparent to the backend.
def isProven (cond : Condition) : Bool :=
  !cond.expr.isMVar

nonrec def instantiateMVars (cond : Condition) : MetaM Condition := do
  return { cond with
    expr  := ← instantiateMVars cond.expr
    type  := ← instantiateMVars cond.type
    mvars := ← cond.mvars.removeAssigned
  }
