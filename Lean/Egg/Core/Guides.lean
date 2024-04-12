import Egg.Core.Source
import Lean
open Lean

namespace Egg

structure Guide where
  expr : Expr
  src  : Source

abbrev Guides := Array Guide
