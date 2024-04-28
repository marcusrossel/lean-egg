import Egg

variable (thm₁ : {α : Type}   → [Add α] → (a b : α) → a + b = b + a)
variable (thm₂ : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

example {a b : Nat} : a + b = b + a := by
  egg [thm₁]

example {a b : Nat} : a + b = b + a := by
  egg [thm₂]
