import Egg.Lean
import Lean
open Lean

namespace Egg.MVars

structure Ambient where
  expr : MVarIdSet
  lvl  : LMVarIdSet

namespace Ambient

instance : EmptyCollection Ambient where
  emptyCollection := { expr := ∅, lvl := ∅ }

-- TODO: How can we collect ambient lmvars?
def collect : MetaM MVars.Ambient := do
  let expr := (← getMCtx).decls.foldl (init := ∅) fun result m _ => result.insert m
  return { expr, lvl := ∅ }

def unassigned (amb : Ambient) : MetaM (MVarIdSet × LMVarIdSet) := do
  let expr ← amb.expr.filterM fun mvar  => return !(← mvar.isAssigned)
  let lvl  ← amb.lvl.filterM  fun lmvar => return !(← isLevelMVarAssigned lmvar)
  return (expr, lvl)
