import Egg.Lean
import Lean
open Lean Meta

namespace Egg

structure MVars where
  expr : MVarIdSet  := ∅
  lvl  : LMVarIdSet := ∅
  -- A subset of `expr` which tracks the mvars whose type is a type class.
  tc   : MVarIdSet  := ∅
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

private partial def collectMVars : Expr → MVarCollectionState → MetaM MVarCollectionState
  | .mvar id                                         => visitMVar id
  | .const _ lvls                                    => (return visitConst lvls ·)
  | .sort lvl                                        => (return visitSort lvl ·)
  | .proj _ _ e | .mdata _ e                         => visit e
  | .forallE _ e₁ e₂ _ | .lam _ e₁ e₂ _ | .app e₁ e₂ => visit e₁ >=> visit e₂
  | .letE _ e₁ e₂ e₃ _                               => visit e₁ >=> visit e₂ >=> visit e₃
  | _                                                => pure
where
  visit (e : Expr) (s : MVarCollectionState) : MetaM MVarCollectionState :=
    if !e.hasMVar || s.visitedExprs.contains e then
      return s
    else
      collectMVars e { s with visitedExprs := s.visitedExprs.insert e }

  visitMVar (id : MVarId) (s : MVarCollectionState) : MetaM MVarCollectionState :=
    return { s with mvars := ← s.mvars.insertExpr id }

  visitConst (lvls : List Level) (s : MVarCollectionState) : MVarCollectionState := Id.run do
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

  visitSort (lvl : Level) (s : MVarCollectionState) : MVarCollectionState :=
    if s.visitedLvls.contains lvl then
      s
    else
      { s with
        mvars.lvl := lvl.collectMVars s.mvars.lvl
        visitedLvls := s.visitedLvls.insert lvl
      }

namespace MVars

def collect (e : Expr) : MetaM MVars :=
  MVarCollectionState.mvars <$> collectMVars e {}

def merge (vars₁ vars₂ : MVars) : MVars where
  expr := vars₁.expr.merge vars₂.expr
  lvl := vars₁.lvl.merge vars₂.lvl

def removeAssigned (mvars : MVars) : MetaM MVars := do
  return {
    expr := ← mvars.expr.filterM fun var => return !(← var.isAssigned)
    lvl  := ← mvars.lvl.filterM  fun var => return !(← isLevelMVarAssigned var)
    tc   := ← mvars.tc.filterM   fun var => return !(← var.isAssigned)
  }
