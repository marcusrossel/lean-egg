import Egg

theorem t [Add α] (a b : α) : a + b = b + a :=
  sorry

example {a b : Nat} : a + b = b + a := by
  egg [t]
