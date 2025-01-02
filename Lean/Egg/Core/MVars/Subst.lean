import Egg.Core.MVars.Basic
import Lean
open Lean hiding HashMap
open Meta
open Std (HashMap)

namespace Egg.MVars

structure Subst where
  expr : HashMap MVarId  MVarId
  lvl  : HashMap LMVarId LMVarId

instance : EmptyCollection Subst where
  emptyCollection := { expr := ∅, lvl := ∅ }

namespace Subst

def insertExpr (subst : Subst) (m m' : MVarId) : Subst :=
  { subst with expr := subst.expr.insert m m' }

def insertLevel (subst : Subst) (m m' : LMVarId) : Subst :=
  { subst with lvl := subst.lvl.insert m m' }

def apply (subst : Subst) (e : Expr) : Expr :=
  e.replace replaceExpr
where
  replaceExpr : Expr → Option Expr
  | .mvar id         => subst.expr[id]? >>= (Expr.mvar ·)
  | .sort lvl        => Expr.sort <| lvl.replace replaceLvl
  | .const name lvls => Expr.const name <| lvls.map (·.replace replaceLvl)
  | _                => none
  replaceLvl : Level → Option Level
  | .mvar id => subst.lvl[id]? >>= (Level.mvar ·)
  | _        => none

end Subst

def fresh (mvars : MVars) (init : Subst := {}) : MetaM (MVars × Subst) := do
  let mut subst := init
  let mut mvars' : MVars := {}
  -- Assigns fresh expression mvars.
  for (m, ps) in mvars.expr do
    if let some m' := subst.expr[m]? then
      mvars' := mvars'.insertExpr m' ps
    else
      let m' := (← mkFreshExprMVar none).mvarId!
      subst  := subst.insertExpr m m'
      mvars' := mvars'.insertExpr m' ps
  -- Assigns fresh level mvars.
  for (m, ps) in mvars.lvl do
    if let some m' := subst.lvl[m]? then
      mvars' := mvars'.insertLevel m' ps
    else
      let m' := (← mkFreshLevelMVar).mvarId!
      subst  := subst.insertLevel m m'
      mvars' := mvars'.insertLevel m' ps
  -- As the type of an mvar may also contain mvars, we also have to replace those type-level mvars
  -- with their fresh counterpart. We can only do this once we know the fresh counterpart for each
  -- mvar, so we postpone the type assignment until now (that is, the type given for
  -- `mkFreshExprMVar` above was `none`).
  -- TODO: What about mvars contained in the type of the type, etc.?
  for (m, _) in mvars.expr do
    subst.expr[m]!.setType <| subst.apply (← m.getType)
  return (mvars', subst)
