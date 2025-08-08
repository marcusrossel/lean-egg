import Egg

-- This test checks that level mvars are not encoded as pattern variables when they shouldn't be.
--
-- This used to crash because the encoding of the goal contained pattern variables. The underlying
-- reason is that the encoding of level mvars (as a pattern variable or constant) is decided by
-- `isLevelMVarAssignable`. And for certain cases we did not bump the mctx depth correctly.

class AddComm (α : Type _) extends Add α where
  comm : ∀ (a b : α), a + b = b + a

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
instance (α : Type _) [Add α] : AddComm α where
  comm a b := by egg
