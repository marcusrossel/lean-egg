import Egg

-- TODO: What is this testing?

variable (thm : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

-- TODO: It feels like this is related to universe levels.
example {a b : Nat} : a + b = b + a := by
  sorry -- egg [thm]
