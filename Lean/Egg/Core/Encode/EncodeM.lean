import Egg.Core.Config
import Egg.Core.Source
import Egg.Core.MVars.Ambient
open Lean hiding HashMap
open Std (HashMap)

namespace Egg

abbrev Expression := String

structure EncodeM.State where
  config : Config.Encoding
  bvars  : List FVarId := []
  amb    : MVars.Ambient
  cache  : HashMap Expr Expression := ∅

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
    let a ← m s!"${fvar.fvarId!.uniqueIdx!}" (body.instantiate #[fvar])
    set { s with bvars := s.bvars }
    return a

def representsBVar (id : FVarId) : EncodeM Bool := do
  return (← get).bvars.contains id

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
