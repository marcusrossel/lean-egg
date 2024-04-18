import Egg.Core.Config
import Egg.Core.Source
import Std.Data.List.Basic

open Lean

namespace Egg

structure EncodeM.State where
  exprSrc : Source
  config  : Config.Encoding
  bvars   : List FVarId := []

abbrev EncodeM := StateT EncodeM.State MetaM

namespace EncodeM

def exprSrc : EncodeM Source :=
  State.exprSrc <$> get

def config : EncodeM Config.Encoding :=
  State.config <$> get

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
