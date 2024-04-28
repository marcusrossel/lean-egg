import Egg.Core.Source
import Egg.Core.Normalize
import Lean
open Lean

namespace Egg

structure Guide where
  private mk ::
  expr : Expr
  src  : Source

def Guide.from (expr : Expr) (src : Source) : MetaM Guide :=
  return { expr := ← normalize expr .noReduce, src }

abbrev Guides := Array Guide
