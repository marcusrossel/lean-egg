import Egg.Lean
import Lean
open Lean Meta

namespace Egg

structure MVars where
  expr : MVarIdSet  := ∅
  lvl  : LMVarIdSet := ∅
  -- A subset of `expr` which tracks the mvars whose type is a type class.
  tc   : MVarIdSet  := ∅

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

protected structure Subst.Expr where
  fwd : HashMap MVarId MVarId := ∅
  bwd : HashMap MVarId MVarId := ∅

protected abbrev Subst.Lvl := HashMap LMVarId LMVarId

structure Subst where
  expr : Subst.Expr := {}
  lvl  : Subst.Lvl  := ∅

def Subst.apply (subst : Subst) (e : Expr) : Expr :=
  e.replace replaceExpr
where
  replaceExpr : Expr → Option Expr
  | .mvar id         => subst.expr.fwd.find? id >>= (Expr.mvar ·)
  | .sort lvl        => Expr.sort <| lvl.replace replaceLvl
  | .const name lvls => Expr.const name <| lvls.map (·.replace replaceLvl)
  | _                => none

  replaceLvl : Level → Option Level
  | .mvar id => subst.lvl.find? id >>= (Level.mvar ·)
  | _        => none

def fresh (mvars : MVars) (init : Subst := {}) : MetaM (MVars × Subst) := do
  let (exprVars, exprSubst) ← freshExprs mvars.expr init.expr
  let (lvlVars, lvlSubst) ← freshLvls mvars.lvl init.lvl
  let subst := { expr := exprSubst, lvl := lvlSubst }
  assignFreshExprMVarTypes exprVars subst
  return ({ expr := exprVars, lvl := lvlVars }, subst)
where
  freshExprs (src : MVarIdSet) (subst : Subst.Expr) : MetaM (MVarIdSet × Subst.Expr) := do
    let mut vars : MVarIdSet := {}
    let mut subst := subst
    for var in src do
      if let some f := subst.fwd.find? var then
        vars := vars.insert f
      else
        -- Note: As the type of an mvar may also contain mvars, we also have to replace mvars with
        --       their fresh counterpart *in the type*. We can only do this once we know the fresh
        --       counterpart for each mvar, so we postpone the type assignment.
        let f ← mkFreshExprMVar none
        subst := {
          fwd := subst.fwd.insert var f.mvarId!
          bwd := subst.bwd.insert f.mvarId! var
        }
        vars := vars.insert f.mvarId!
    return (vars, subst)

  freshLvls (src : LMVarIdSet) (subst : Subst.Lvl) : MetaM (LMVarIdSet × Subst.Lvl) := do
    let mut vars : LMVarIdSet := {}
    let mut subst := subst
    for var in src do
      if let some f := subst.find? var then
        vars := vars.insert f
      else
        let f ← mkFreshLevelMVar
        subst := subst.insert var f.mvarId!
        vars := vars.insert f.mvarId!
    return (vars, subst)

  assignFreshExprMVarTypes (vars : MVarIdSet) (subst : Subst) : MetaM Unit := do
    for var in vars do
      let srcType ← (subst.expr.bwd.find! var).getType
      let freshType := subst.apply srcType
      var.setType freshType

def removeAssigned (mvars : MVars) : MetaM MVars := do
  return {
    expr := ← mvars.expr.filterM fun var => return !(← var.isAssigned)
    lvl  := ← mvars.lvl.filterM  fun var => return !(← isLevelMVarAssigned var)
    tc   := ← mvars.tc.filterM   fun var => return !(← var.isAssigned)
  }
