import Egg.Core.MVars.Basic
import Lean
open Lean

namespace Egg.MVars

abbrev Ambient := MVarIdSet

def Ambient.get : MetaM Ambient := do
  let mut result := ∅
  for (mvar, _) in (← getMCtx).decls do
    if !(← mvar.isAssigned) then
      result := result.insert mvar
  return result

def remove (mvars : MVars) (amb : Ambient) : MVars where
  expr := mvars.expr.filter (!amb.contains ·)
  lvl  := mvars.lvl
  tc   := mvars.tc.filter (!amb.contains ·)
