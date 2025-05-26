import Egg

-- This test should fail, because both directions of `h` are invalid, because the `Nat` argument is
-- not covered, because it can't be a condition, because it's neither a proof nor an instance.

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : Nat → 0 = 1) : 0 = 1 := by
  egg [h]
