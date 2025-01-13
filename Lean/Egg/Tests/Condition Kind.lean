import Egg

/-- error: Rewrite #0 requires condition of type 'Nat' which is neither a proof nor an instance. -/
#guard_msgs in
example (h : Nat → 0 = 1) : 0 = 1 := by
  egg [h]
