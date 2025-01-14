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
      let g ← Tactic.elabTerm g none
      -- For some reason Lean introduces the term `sorry = true` if the list of guides is empty.
      -- This expression contains an mvar which results in a guide term with a pattern variable,
      -- which crashed egg. So we filter for this here.
      if g.hasSorry then continue
      let guide ← Guide.from g (.guide idx (derived := false))
      guides := guides.push guide
    return guides
  | _ => unreachable!
