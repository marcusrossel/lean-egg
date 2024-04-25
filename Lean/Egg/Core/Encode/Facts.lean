import Egg.Core.Premise.Facts
import Egg.Core.Encode.Basic
import Lean
open Lean

namespace Egg

abbrev Fact.Encoded := Expression

abbrev Facts.Encoded := Array Fact.Encoded

def Facts.encode (facts : Facts) (cfg : Config.Encoding) (amb : MVars.Ambient) :
    MetaM Facts.Encoded :=
  facts.mapM fun fact => Egg.encode fact.type fact.src cfg amb
