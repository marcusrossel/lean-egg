import Egg.Core.Source
import Egg.Core.Normalize
import Lean
open Lean

namespace Egg.Fact

inductive Kind where
  | proof
  | tcInst

def Kind.forType? (ty : Expr) : MetaM (Option Fact.Kind) := do
  if ← Meta.isProp ty then
    return some .proof
  else if (← Meta.isClass? ty).isSome then
    return some .tcInst
  else
    return none

-- Note: We don't create `Fact`s directly, but use `Fact.from` instead.
structure _root_.Egg.Fact where
  private mk ::
  kind  : Kind
  proof : Expr
  type  : Expr
  src   : Source

def from? (proof : Expr) (type : Expr) (src : Source) : MetaM (Option Fact) := do
  let type ← normalize type .noReduce
  let some kind ← Kind.forType? type | return none
  return some { kind, src, type, proof }

end Fact

abbrev Facts := Array Fact
