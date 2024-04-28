import Egg.Core.Config
import Egg.Core.Source
import Egg.Core.MVars.Ambient
import Std.Data.List.Basic

open Lean

namespace Egg

structure EncodeM.State where
  config  : Config.Encoding
  bvars   : List FVarId := []
  amb     : MVars.Ambient

abbrev EncodeM := StateT EncodeM.State MetaM

namespace EncodeM

def config : EncodeM Config.Encoding :=
  State.config <$> get

def isAmbientExpr (mvar : MVarId) : EncodeM Bool := do
  return (← get).amb.expr.contains mvar

def isAmbientLvl (lmvar : LMVarId) : EncodeM Bool := do
  return (← get).amb.lvl.contains lmvar

-- Note: This only works as intended if `m` does not add any additional bvars (permanently).
def withInstantiatedBVar (ty body : Expr) (m : Expr → EncodeM α) : EncodeM α := do
  Meta.withLocalDecl .anonymous .default ty fun fvar => do
    let s ← get
    set { s with bvars := fvar.fvarId! :: s.bvars }
    let a ← m (body.instantiate #[fvar])
    set { s with bvars := s.bvars }
    return a

def bvarIdx? (id : FVarId) : EncodeM (Option Nat) := do
  return (← get).bvars.indexOf? id

def needsProofErasure (e : Expr) : EncodeM Bool := do
  (return (← config).eraseProofs) <&&> Meta.isProof e
