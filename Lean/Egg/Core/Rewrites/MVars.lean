import Egg.Lean
import Lean
open Lean

namespace Egg.Rewrite

structure MVars where
  expr : MVarIdSet  := ∅
  lvl  : LMVarIdSet := ∅

def MVars.merge (vars₁ vars₂ : MVars) : MVars where
  expr := vars₁.expr.merge vars₂.expr
  lvl := vars₁.lvl.merge vars₂.lvl

private structure MVarCollectionState where
  visitedExprs : ExprSet  := {}
  visitedLvls  : LevelSet := {}
  mvars        : MVars    := {}

private partial def collectMVars : Expr → MVarCollectionState → MVarCollectionState
  | .mvar id                                         => visitMVar id
  | .const _ lvls                                    => visitConst lvls
  | .sort lvl                                        => visitSort lvl
  | .proj _ _ e | .mdata _ e                         => visit e
  | .forallE _ e₁ e₂ _ | .lam _ e₁ e₂ _ | .app e₁ e₂ => visit e₁ ∘ visit e₂
  | .letE _ e₁ e₂ e₃ _                               => visit e₁ ∘ visit e₂ ∘ visit e₃
  | _                                                => id
where
  visit (e : Expr) (s : MVarCollectionState) : MVarCollectionState :=
    if !e.hasMVar || s.visitedExprs.contains e then
      s
    else
      collectMVars e { s with visitedExprs := s.visitedExprs.insert e }

  visitMVar (id : MVarId) (s : MVarCollectionState) : MVarCollectionState := { s with
    mvars.expr := s.mvars.expr.insert id
  }

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

def MVars.collect (e : Expr) : MVars :=
  collectMVars e {} |>.mvars
