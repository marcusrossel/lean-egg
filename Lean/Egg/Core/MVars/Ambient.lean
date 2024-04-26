import Egg.Core.MVars.Basic
import Lean
open Lean

namespace Egg.MVars

abbrev Ambient.Expr := PersistentHashMap MVarId MetavarDecl

abbrev Ambient.Level := LMVarIdSet

structure Ambient where
  expr : Ambient.Expr
  lvl  : Ambient.Level

namespace Ambient

def Expr.get : MetaM Ambient.Expr :=
  return (← getMCtx).decls

def unassigned (amb : Ambient) : MetaM (MVarIdSet × LMVarIdSet) := do
  let expr ← amb.expr.foldlM (init := ∅) fun res mvar _ =>
    return if !(← mvar.isAssigned) then res.insert mvar else res
  let lvl ← amb.lvl.filterM fun lmvar => return !(← isLevelMVarAssigned lmvar)
  return (expr, lvl)

end Ambient

def remove (mvars : MVars) (amb : Ambient) : MVars where
  expr := mvars.expr.filter (!amb.expr.contains ·)
  lvl  := mvars.lvl.filter (!amb.lvl.contains ·)
  tc   := mvars.tc.filter (!amb.expr.contains ·)
