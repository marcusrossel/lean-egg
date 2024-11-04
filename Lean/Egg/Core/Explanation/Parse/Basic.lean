import Egg.Core.Explanation.Parse.Shared
import Egg.Core.Explanation.Parse.Egg
import Egg.Core.Explanation.Parse.Slotted
import Lean

open Lean

namespace Egg.Explanation

-- Note: This could be generalized to any monad with an environment and exceptions.
def Raw.parse (raw : Explanation.Raw) : MetaM Explanation := do
  let (str, stx_cat) :=
    if raw.slotted
    then (raw.str.replace "$" "", `slotted_expl) -- HACK
    else (raw.str, `egg_expl)
  match Parser.runParserCategory (← getEnv) stx_cat str with
  | .ok stx    => if raw.slotted then parseSlottedExpl ⟨stx⟩ else parseEggExpl ⟨stx⟩
  | .error err => throwError s!"{ParseError.msgPrefix}\n{err}\n\n{raw.str}"
