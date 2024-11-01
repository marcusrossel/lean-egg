import Egg.Core.Config
import Egg.Core.Source
import Egg.Core.MVars.Ambient
open Lean hiding HashMap
open Std (HashMap)

namespace Egg

abbrev Expression := String

structure EncodeM.State where
  config     : Config.Encoding
  bvars      : List FVarId := []
  amb        : MVars.Ambient
  cache      : HashMap Expr Expression := ∅
  usedBinder : Bool := false

abbrev EncodeM := StateT EncodeM.State MetaM

namespace EncodeM

def config : EncodeM Config.Encoding :=
  State.config <$> get

def isAmbientExpr (mvar : MVarId) : EncodeM Bool := do
  return (← get).amb.expr.contains mvar

def isAmbientLvl (lmvar : LMVarId) : EncodeM Bool := do
  return (← get).amb.lvl.contains lmvar

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
  let some bvarIdx := (← get).bvars.indexOf? id | return none
  return if (← config).slotted then s!"${id.uniqueIdx!}" else s!"{bvarIdx}"

def needsProofErasure (e : Expr) : EncodeM Bool := do
  (return (← config).eraseProofs) <&&> Meta.isProof e

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

def setUsedBinder : EncodeM Unit :=
  modify ({ · with usedBinder := true })
