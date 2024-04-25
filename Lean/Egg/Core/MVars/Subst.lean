import Egg.Core.MVars.Basic
import Lean
open Lean Meta

namespace Egg.MVars

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

def fresh' (mvars : Array MVars) (init : Subst := {}) : MetaM (Array MVars × Subst) := do
  let mut subst := init
  let mut fresh := #[]
  for m in mvars do
    let (f, s) ← m.fresh (init := subst)
    fresh := fresh.push f
    subst := s
  return (fresh, subst)
