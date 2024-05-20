import Egg

set_option egg.conditionSubgoals true

example (a : Nat) (h : True → a = b) : a = b := by
  sorry
  -- egg [h]
  -- constructor
