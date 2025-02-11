import Egg

variable (thm₁ : {α : Type} → [Add α] → (a b : α) → a + b = b + a)
variable (thm₂ : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

example {a b : Nat} : a + b = b + a := by
  egg [thm₁]

-- TODO: This started failing after bumping to egg v0.10.0.
--       Interestingly `have := @thm₂ Nat` works.
example {a b : Nat} : a + b = b + a := by
  sorry -- egg [thm₂]
