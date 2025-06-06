import Egg.Core.MVars.Basic
import Lean

open Lean Meta

namespace Egg.MVars.CollectionM

private structure State where
  mvars  : MVars
  active : Properties

private abbrev _root_.Egg.MVars.CollectionM := StateT CollectionM.State MetaM

private nonrec def run (m : CollectionM Unit) : MetaM MVars := do
  let (_, state) ← m.run { mvars := {}, active := ∅ }
  return state.mvars

private def active : CollectionM Properties :=
  return (← get).active

private def withProperty (p : Property) (m : CollectionM α) : CollectionM α := do
  let { active, .. } ← getModify fun s => { s with active := s.active.insert p }
  let a ← m
  modify ({ · with active })
  return a

private def collectMVar (mvar : MVarId) : CollectionM Unit := do
  unless ← mvar.isAssignable do return
  let isTcInst ← Meta.isTCInstance (.mvar mvar)
  let isProof  ← Meta.isProof (.mvar mvar)
  modify fun s =>
    let ps := s.active
      |>.insertIf isTcInst .isTcInst
      |>.insertIf (isProof && !isTcInst) .isProof
    let ps := ps.insertIf ps.isEmpty .unconditionallyVisible
    { s with mvars := s.mvars.insertExpr mvar ps }

private def collectLMVar (lmvar : LMVarId) : CollectionM Unit := do
  unless ← isLevelMVarAssignable lmvar do return
  modify fun s =>
    let ps := s.active.insertIf s.active.isEmpty .unconditionallyVisible
    { s with mvars := s.mvars.insertLevel lmvar ps }

private def collectLevel (lvl : Level) : CollectionM Unit := do
  for lmvar in lvl.collectMVars do collectLMVar lmvar

private def collectLevels (lvls : List Level) : CollectionM Unit := do
  for lvl in lvls do collectLevel lvl

private partial def collect (e : Expr) : CollectionM Unit := do
  -- We check if `e` is an ambient mvar here (as opposed to only checking for ambient mvars in
  -- `collect{L}MVar`), in order to avoid looking at its type in that case.
  if ← e.isAmbientMVar then
    return
  else if ← Meta.isTCInstance e then
    -- We don't want mvars which are `.isTcInst` to also be tagged with `.inTcInstTerm`, if they
    -- don't appear within another type class instance term. Thus, we check whether `m` is an mvar
    -- to avoid the `withProperty .inTcInstTerm` in that case.
    if let .mvar m := e then collectMVar m else withProperty .inTcInstTerm do core e
    withProperty .inErasedTcInst do core (← inferType e)
  else if ← Meta.isProof e then
    -- We don't want mvars which are `.isProof` to also be tagged with `.inProofTerm`, if they don't
    -- appear within another proof term. Thus, we check whether `m` is an mvar to avoid the
    -- `withProperty .inProofTerm` in that case.
    if let .mvar m := e then collectMVar m else withProperty .inProofTerm do core e
    withProperty .inErasedProof do core (← inferType e)
  else if let (.app (.app (.app (.const ``Eq [u]) t) lhs) rhs) := e then
    withProperty .inEqType do collectLevel u; core t
    core lhs; core rhs
  else
    core e
where
  core (e : Expr) : CollectionM Unit := do
    unless e.hasMVar do return
    match e with
    | .mvar id      => collectMVar id
    | .const _ lvls => collectLevels lvls
    | .sort lvl     => collectLevel lvl
    | .app fn arg   => coreRec fn; coreRec arg
    | .forallE _ ty b _ | .lam _ ty b _ =>
      coreRec ty
      withLocalDecl .anonymous .default ty fun fvar => coreRec (b.instantiate #[fvar])
    | .letE .. | .mdata .. | .proj .. =>
      panic! "'Egg.MVars.CollectionM.collect.core' received non-normalized expression"
    -- Note: This should not be reachable as we check whether `e` contains mvars at the beginning.
    | _ => return

  -- When `core` performs a recursive call, we choose whether to call `core` or `collect` depending
  -- on whether there are any active properties. If there already is an active property, then we
  -- don't want to consider additional properties and simply call `core` again. If there are no
  -- active properties yet, then we call `collect` which checks whether a property is satisfied.
  coreRec (e : Expr) : CollectionM Unit := do
    if (← active).isEmpty then collect e else core e

end CollectionM

def collect (e : Expr) : MetaM MVars :=
  CollectionM.collect e |>.run
