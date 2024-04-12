import Egg.Core.Guides
import Lean
open Lean Elab Tactic

namespace Egg.Guides

declare_syntax_cat egg_guides
syntax " via " (term,*) : egg_guides

def parseGuides : TSyntax `egg_guides → TacticM Guides
  | `(egg_guides|via $gs,*) => do
    let mut guides : Guides := #[]
    for g in gs.getElems, idx in [:gs.getElems.size] do
      let guide ← Guide.from (← Tactic.elabTerm g none) (.guide idx)
      guides := guides.push guide
    return guides
  | _ => unreachable!
