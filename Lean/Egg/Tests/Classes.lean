import Egg

variable (thm : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

example {a b : Nat} : a + b = b + a := by
  egg [thm]
