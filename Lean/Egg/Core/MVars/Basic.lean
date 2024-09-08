import Egg.Lean
import Lean
open Lean Meta

namespace Egg

structure MVars where
  expr : MVarIdSet := ∅
  lvl : LMVarIdSet := ∅
  -- The subset of `expr` of mvars whose type is a type class.
  tc : MVarIdSet := ∅
  -- The set of mvars which appear in proof terms. This is only populated if `MVars.collect` is
  -- called with `proofErasure := true`. Note that it is not necessarily (and likely not) a subset
  -- of `expr`.
  proof : MVarIdSet := ∅
  deriving Inhabited

private def MVars.insertExpr (mvars : MVars) (id : MVarId) : MetaM MVars := do
  let isClass := (← isClass? (← id.getType)).isSome
  return { mvars with
      expr := mvars.expr.insert id
      tc   := if isClass then mvars.tc.insert id else mvars.tc
  }

private structure MVarCollectionState where
  visitedExprs : ExprSet  := {}
  visitedLvls  : LevelSet := {}
  mvars        : MVars    := {}

private partial def collectMVars (e : Expr) (s : MVarCollectionState) (proofErasure : Bool) :
    MetaM MVarCollectionState := do
  if ← (return proofErasure) <&&> (Meta.isProof e) then
    let s' ← core (isProof := true) e s
    core (isProof := false) (← inferType e) s'
  else
    core (isProof := false) e s
where
  core (isProof : Bool) : Expr → MVarCollectionState → MetaM MVarCollectionState
    | .mvar id                                         => visitMVar isProof id
    | .const _ lvls                                    => (return visitConst isProof lvls ·)
    | .sort lvl                                        => (return visitSort isProof lvl ·)
    | .proj _ _ e | .mdata _ e                         => visit isProof e
    | .forallE _ e₁ e₂ _ | .lam _ e₁ e₂ _ | .app e₁ e₂ => (withLocalDecl .anonymous .default e₁ fun fvar => (visit isProof e₁ >=> visit isProof (e₂.instantiate #[fvar])) ·)
    | .letE _ e₁ e₂ e₃ _                               => (withLocalDecl .anonymous .default e₁ fun fvar => (visit isProof e₁ >=> visit isProof e₂ >=> visit isProof (e₃.instantiate #[fvar])) ·)
    | _                                                => pure

  visit (isProof : Bool) (e : Expr) (s : MVarCollectionState) : MetaM MVarCollectionState :=
    if !e.hasMVar || s.visitedExprs.contains e then
      return s
    else
      let s' := { s with visitedExprs := s.visitedExprs.insert e }
      if isProof then core isProof e s' else collectMVars e s' proofErasure

  visitMVar (isProof : Bool) (id : MVarId) (s : MVarCollectionState) : MetaM MVarCollectionState :=
    if isProof
    then return { s with mvars.proof := s.mvars.proof.insert id }
    else return { s with mvars := ← s.mvars.insertExpr id }

  visitConst (isProof : Bool) (lvls : List Level) (s : MVarCollectionState) :
      MVarCollectionState := Id.run do
    if isProof then
      return s
    else
      let mut s := s
      for lvl in lvls do
        if s.visitedLvls.contains lvl then
          continue
        else
          s := { s with
            mvars.lvl := lvl.collectMVars s.mvars.lvl
            visitedLvls := s.visitedLvls.insert lvl
          }
      return s

  visitSort (isProof : Bool) (lvl : Level) (s : MVarCollectionState) : MVarCollectionState :=
    if isProof then
      s
    else
      if s.visitedLvls.contains lvl then
        s
      else
        { s with
          mvars.lvl := lvl.collectMVars s.mvars.lvl
          visitedLvls := s.visitedLvls.insert lvl
        }

namespace MVars

def collect (e : Expr) (proofErasure : Bool) : MetaM MVars :=
  MVarCollectionState.mvars <$> collectMVars e {} proofErasure

def merge (vars₁ vars₂ : MVars) : MVars where
  expr  := vars₁.expr.merge vars₂.expr
  lvl   := vars₁.lvl.merge vars₂.lvl
  tc    := vars₁.tc.merge vars₂.tc
  proof := vars₁.proof.merge vars₂.proof

def removeAssigned (mvars : MVars) : MetaM MVars := do
  return {
    expr  := ← mvars.expr.filterM  fun var => return !(← var.isAssigned)
    lvl   := ← mvars.lvl.filterM   fun var => return !(← isLevelMVarAssigned var)
    tc    := ← mvars.tc.filterM    fun var => return !(← var.isAssigned)
    proof := ← mvars.proof.filterM fun var => return !(← var.isAssigned)
  }
