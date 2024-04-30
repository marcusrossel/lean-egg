import Egg.Core.Premise.Facts
import Egg.Core.Encode.Basic
import Lean
open Lean

namespace Egg

abbrev Fact.Encoded := Expression

abbrev Facts.Encoded := Array Fact.Encoded

def Facts.encode (facts : Facts) (cfg : Config.Encoding) (amb : MVars.Ambient) :
    MetaM Facts.Encoded :=
  facts.filterMapM fun fact => do
    if cfg.useRwsAsFacts || !fact.isRw
    then Egg.encode fact.type cfg amb
    else return none
