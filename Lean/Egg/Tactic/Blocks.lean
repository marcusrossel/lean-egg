import Egg.Core.Blocks
import Lean
open Lean Elab Tactic

namespace Egg.Blocks

declare_syntax_cat egg_blocks
syntax " blocking " (term,*) : egg_blocks

def parseBlocks (cfg : Config.Normalization) : TSyntax `egg_blocks → TacticM Blocks
  | `(egg_blocks|blocking $bs,*) => do
    let mut blocks : Blocks := #[]
    for b in bs.getElems do
      let e ← Tactic.elabTerm b none
      -- See `parseGuides` for an explanation of this.
      if e.hasSorry then continue
      let some block ← Block.from? e cfg | throwErrorAt b "blocking terms must be propositions"
      blocks := blocks.push block
    return blocks
  | _ => unreachable!
