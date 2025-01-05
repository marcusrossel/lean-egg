import Egg.Core.Guides
import Lean
open Lean Elab Tactic

namespace Egg.Guides

declare_syntax_cat egg_guides
syntax &" using " (term,*) : egg_guides

def parseGuides : TSyntax `egg_guides → TacticM Guides
  | `(egg_guides|using $gs,*) => do
    let mut guides : Guides := #[]
    for g in gs.getElems, idx in [:gs.getElems.size] do
      let guide ← Guide.from (← Tactic.elabTerm g none) (.guide idx (derived := false))
      guides := guides.push guide
    return guides
  | _ => unreachable!
