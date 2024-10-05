import Egg

-- Checks that we rerun with shapes when proof reconstruction fails. Without this feature, this test
-- case would fail during proof reconstruction with the explanation shown when setting
-- `exitPoint := some .beforeProof`.

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg [h]
