import Egg.Core.Premise.Facts
import Egg.Core.Encode.Basic
import Lean
open Lean

namespace Egg

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Fact.Encoded where
  name : String
  expr : Expression

abbrev Facts.Encoded := Array Fact.Encoded

def Facts.encode (facts : Facts) (cfg : Config.Encoding) (amb : MVars.Ambient) :
    MetaM Facts.Encoded :=
  facts.filterMapM fun fact => do
    unless cfg.useRwsAsFacts || !fact.isRw do return none
    return some {
      name := fact.src.description,
      expr := ← Egg.encode fact.type cfg amb
    }
