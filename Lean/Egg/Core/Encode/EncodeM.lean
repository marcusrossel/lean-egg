import Egg.Core.Config
import Egg.Core.Source
open Lean hiding HashMap
open Std (HashMap)

namespace Egg

abbrev Expression := String

structure EncodeM.State where
  config : Config.Encoding
  bvars  : List FVarId := []
  cache  : HashMap Expr Expression := ∅

abbrev EncodeM := StateT EncodeM.State MetaM

namespace EncodeM

def config : EncodeM Config.Encoding :=
  State.config <$> get

-- Note: This only works as intended if `m` does not add any additional bvars (permanently).
def withInstantiatedBVar (ty body : Expr) (m : String → Expr → EncodeM α) : EncodeM α := do
  Meta.withLocalDecl .anonymous .default ty fun fvar => do
    let s ← get
    set { s with bvars := fvar.fvarId! :: s.bvars }
    let bvarName := if (← config).slotted then s!"${fvar.fvarId!.uniqueIdx!} " else ""
    let a ← m bvarName (body.instantiate #[fvar])
    set { s with bvars := s.bvars }
    return a

def bvarName? (id : FVarId) : EncodeM (Option String) := do
  let some bvarIdx := (← get).bvars.idxOf? id | return none
  return if (← config).slotted then s!"${id.uniqueIdx!}" else s!"{bvarIdx}"

open Meta

def needsProofErasure (e : Expr) : EncodeM Bool := do
  isProof e

def needsInstErasure? (e : Expr) : EncodeM (Option Expr) := do
  let ty ← inferType e
  -- Note: `isClass?` does not require the type operator to be fully applied. That is, if `ty` is
  --       `Inhabited` instead of `Inhabited Nat`, `isClass?` will still succeed. This shouldn't
  --       pose a problem though as long as we traverse terms top-down during encoding. That is, as
  --       long as we always encounter `Inhabited Nat` before we would encounter just `Inhabited`.
  unless (← isClass? ty).isSome do return none
  return ty

def withCache (e : Expr) (m : EncodeM Expression) : EncodeM Expression := do
  let s ← get
  if let some enc := s.cache[e]? then
    return enc
  else
    let enc ← m
    set { s with cache := s.cache.insert e enc }
    return enc

def withoutShapes (m : EncodeM Expression) : EncodeM Expression := do
  let s ← get
  let shapes := s.config.shapes
  set { s with config.shapes := false }
  let enc ← m
  set { s with config.shapes := shapes }
  return enc
