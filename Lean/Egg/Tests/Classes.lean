import Egg

-- TODO: What is this testing?

variable (thm : {α : Type _} → [Add α] → (a b : α) → a + b = b + a)

set_option trace.egg true in
example {a b : Nat} : a + b = b + a := by
  egg [thm]
