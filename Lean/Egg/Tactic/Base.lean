import Lean
open Lean

namespace Egg

declare_syntax_cat egg_base
syntax &" from " ident : egg_base

def parseBase [Monad m] [MonadLCtx m] [MonadError m] : TSyntax `egg_base → m FVarId
  | `(egg_base|from $h) => do
    let lctx ← getLCtx
    let some d := lctx.findFromUserName? h.getId | throwErrorAt h s!"Unknown identifier '{h.getId}'"
    return d.fvarId
  | _ => unreachable!
