import Egg.Core.Source
import Lean
open Lean

namespace Egg

structure Fact where
  src   : Source
  type  : Expr
  proof : Expr

abbrev Facts := Array Fact
