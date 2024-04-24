import Egg.Core.MVars.Basic
import Lean
open Lean

namespace Egg.MVars

abbrev Ambient := PersistentHashMap MVarId MetavarDecl

namespace Ambient

def get : MetaM Ambient :=
  return (← getMCtx).decls

def unassigned (amb : Ambient) : MetaM MVarIdSet :=
  amb.foldlM (init := ∅) fun res mvar _ =>
    return if !(← mvar.isAssigned) then res.insert mvar else res

end Ambient

def remove (mvars : MVars) (amb : Ambient) : MVars where
  expr := mvars.expr.filter (!amb.contains ·)
  lvl  := mvars.lvl
  tc   := mvars.tc.filter (!amb.contains ·)
