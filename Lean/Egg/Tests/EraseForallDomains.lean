import Egg

set_option egg.eraseForallDomains true

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg (config := { eraseForallDomains := false }) [h, Nat.add_zero]

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

-- BUG: the rewrite is actually bidirectional, but the domain is the only reference to the mvar for
--      `α` on the rhs.
variable (h : ∀ (α : Type), (α = α) ↔ (∀ (_ : α), 0 = 0))
example : True = True := by
  sorry -- egg [h]
