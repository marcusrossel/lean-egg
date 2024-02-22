import Egg

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg (config := { eraseForallDomains := false }) [h, Nat.add_zero]

-- BUG: proof reconstruction
example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg (config := { eraseForallDomains := true }) [h, Nat.add_zero]

-- BUG: the rewrite is actually bidirectional, but the domain is the only reference to the mvar for
--      `α` on the rhs.
example (h : ∀ (α : Type), (α = α) ↔ (∀ (a : α), 0 = 0)) : True = True := by
  egg (config := { eraseForallDomains := true }) [h]
