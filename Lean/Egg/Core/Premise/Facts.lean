import Egg.Core.Source
import Egg.Core.Normalize
import Lean
open Lean

namespace Egg

-- Note: We don't create `Fact`s directly, but use `Premise.from` instead.
structure Fact where
  src   : Source
  type  : Expr
  proof : Expr
  isRw  : Bool

abbrev Facts := Array Fact
