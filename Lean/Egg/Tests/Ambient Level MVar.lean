import Egg

variable (thm₁ : {α : Type}   → [Add α] → (a b : α) → a + b = b + a)
variable (thm₂ : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

example {a b : Nat} : a + b = b + a := by
  egg [thm₁]

set_option trace.egg true in
example {a b : Nat} : a + b = b + a := by
  egg [thm₂]
