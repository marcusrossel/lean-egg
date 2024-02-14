import Egg.Core.Config
import Egg.Core.Expression
import Egg.Core.Encode.IndexT
import Egg.Lean
import Egg.Core.Rewrites
import Std.Data.List.Basic

open Lean

namespace Egg

structure EncodeM.State where
  exprSrc : Source
  config  : Egg.Config
  bvars   : List FVarId := []
  appArgs : List Expr := []

abbrev EncodeM := StateT EncodeM.State <| IndexT MetaM

namespace EncodeM

def exprSrc : EncodeM Source :=
  State.exprSrc <$> get

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

-- Note: If `m` changes the value of `typeTags`, this change will not be preserved.
def withTypeTags (typeTags : Config.TypeTags) (m : EncodeM α) : EncodeM α := do
  let s ← get
  set { s with config.typeTags := typeTags }
  let a ← m
  set { s with config.typeTags := s.config.typeTags }
  return a

-- Note: If `m` changes the value of `appArgs`, this change will not be preserved.
def withAppArg (arg : Expr) (m : EncodeM α) : EncodeM α := do
  let s ← get
  set { s with appArgs := arg :: s.appArgs }
  let a ← m
  set { s with appArgs := s.appArgs }
  return a

-- Note: If `m` changes the value of `appArgs`, this change will not be preserved.
def withEmptyAppArgs (m : EncodeM α) : EncodeM α := do
  let s ← get
  set { s with appArgs := [] }
  let a ← m
  set { s with appArgs := s.appArgs }
  return a

def saveTcProjIfApplicable (const : Name) (lvls : List Level) : EncodeM Unit := do
  unless (← get).config.genTcProjRws do return
  let some info ← getProjectionFnInfo? const | return
  unless info.fromClass do return
  let args := (← get).appArgs.toArray
  unless args.size > info.numParams do return
  IndexT.saveTcProj { const, lvls, args := args[:info.numParams + 1] } (← get).exprSrc

-- TODO: Only erasing proofs if they don't contain mvars, i.e. if `!e.hasMVar` can cause problems.
--       E.g. if we have a goal equality where the lhs contains a proof term, it will probably
--       be erased as the goal probably doesn't contain any mvars. If we then have a rewrite
--       which should match this lhs, and it contains mvars in the proof term, the proof won't
--       be erased. Thus we won't get a match between the lhs of the goal and the rw as the goal
--       will contain the symbol `proof` while the rewrite will expect an entire expression.
--       I think the reason we didn't want to erase proofs containing mvars is that they might
--       be relevant for proof reconstruction, so let's revisit this when we try to add proof
--       reconstruction for proof erased explanations.
def needsProofErasure (e : Expr) : EncodeM Bool := do
  (return (← config).eraseProofs) <&&>
  -- (return !e.hasMVar) <&&>
  Meta.isProof e
