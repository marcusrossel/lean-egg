import Egg.Core.Explanation.Parse.Shared
import Egg.Core.Explanation.Parse.Egg
import Egg.Core.Explanation.Parse.Slotted
import Lean

open Lean

namespace Egg.Explanation

-- Note: This could be generalized to any monad with an environment and exceptions.
def Raw.parse (raw : Explanation.Raw) : MetaM Explanation := do
  let stx_cat := if raw.slotted then `slotted_expl else `egg_expl
  match Parser.runParserCategory (← getEnv) stx_cat raw.str with
  | .ok stx    =>
    if raw.slotted
    then throwError "Parsing slotted explanations is not implemented yet"
    else parseEggExpl ⟨stx⟩
  | .error err => throwError s!"{ParseError.msgPrefix}\n{err}\n\n{raw.str}"
