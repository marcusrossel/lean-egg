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

def Facts.encode (facts : Facts) (ctx : EncodingCtx) : MetaM Facts.Encoded :=
  facts.mapM fun fact => return {
      name := fact.src.description,
      expr := ← Egg.encode fact.type ctx
    }
