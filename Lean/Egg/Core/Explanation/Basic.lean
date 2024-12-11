import Egg.Core.Source
import Egg.Core.Directions

open Lean

namespace Egg.Explanation

structure Raw where
  str     : String
  slotted : Bool

namespace Rewrite

structure Descriptor where
  src   : Source
  dir   : Direction
  facts : Array Source.Fact
  deriving Inhabited

structure Info extends Descriptor where
  pos? : Option SubExpr.Pos
  deriving Inhabited

end Rewrite

structure Step extends Rewrite.Info where
  dst : Expr
  deriving Inhabited

end Explanation

structure Explanation where
  start : Expr
  steps : Array Explanation.Step
