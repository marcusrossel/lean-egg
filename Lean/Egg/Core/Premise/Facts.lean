import Egg.Core.Source
import Egg.Core.Normalize
import Lean
open Lean

namespace Egg

-- Note: We don't create `Fact`s directly, but use `Fact.from` instead.
structure Fact where
  private mk ::
  proof : Expr
  type  : Expr
  src   : Source

def Fact.«from» (proof : Expr) (type : Expr) (src : Source) : MetaM Fact := do
  let type ← normalize type .noReduce
  return { src, type, proof }

abbrev Facts := Array Fact
