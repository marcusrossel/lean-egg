import Egg

/-- error: egg does not currently support conditional rewrites -/
#guard_msgs in
example (h : ∀ n : Nat, n > 2 → n = 5) : x = 5 := by
  egg [h]
