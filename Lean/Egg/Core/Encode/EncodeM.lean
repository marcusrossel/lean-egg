import Egg.Core.Config
import Egg.Core.Encode.Expression
import Egg.Core.Encode.TypeIndexT
import Std.Data.List.Basic

open Lean

namespace Egg

structure EncodeM.State where
  exprKind : Egg.Expression.Kind
  config   : Egg.Config
  bvars    : List FVarId := []

abbrev EncodeM := StateT EncodeM.State <| TypeIndexT MetaM

namespace EncodeM

def exprKind : EncodeM Egg.Expression.Kind :=
  State.exprKind <$> get

def config : EncodeM Egg.Config:=
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

-- Note: If `m` changes the value of `typeTags` it will not be preserved.
def withTypeTags (typeTags : Config.TypeTags) (m : EncodeM α) : EncodeM α := do
  let s ← get
  set { s with config.typeTags := typeTags }
  let a ← m
  set { s with config.typeTags := s.config.typeTags }
  return a
