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

def Fact.encode (fact : Fact) (ctx : EncodingCtx) : MetaM Fact.Encoded := do
  let type ← Egg.encode fact.type ctx
  let expr := match fact.kind with
    | .proof  => s!"(proof {type})"
    | .tcInst => s!"(inst {type})"
  return { name := fact.src.description, expr }

def Facts.encode (facts : Facts) (ctx : EncodingCtx) : MetaM Facts.Encoded :=
  facts.mapM (Fact.encode · ctx)
