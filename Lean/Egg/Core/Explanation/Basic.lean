import Egg.Core.Source
import Egg.Core.Direction
import Egg.Core.Rewrite.Rule

open Lean

namespace Egg.Explanation

inductive Kind where
  | sameEClass
  | eqTrue

structure Raw where
  kind    : Kind
  str     : String
  slotted : Bool

namespace Rewrite

structure Descriptor where
  id       : Rewrite.Rule.Id
  dir      : Direction
  weakVars : Array (Nat × Nat)
deriving Inhabited

structure Info extends Descriptor where
  pos? : Option SubExpr.Pos
deriving Inhabited

end Rewrite

structure Step extends Rewrite.Info where
  dst : Expr
deriving Inhabited

structure Steps where
  start : Expr
  steps : Array Explanation.Step

end Explanation

structure Explanation extends Explanation.Steps where
  kind  : Explanation.Kind
