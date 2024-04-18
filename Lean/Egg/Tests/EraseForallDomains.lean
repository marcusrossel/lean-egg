import Egg

set_option egg.eraseForallDomains false in
example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

set_option egg.eraseForallDomains true in
example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

-- BUG: The rewrite is actually bidirectional, but the domain is the only reference to the mvar for
--      `α` on the rhs. You can only see this in `trace.egg.encoded`, not `trace.egg.rewrites`.
variable (h : ∀ (α : Type), (α = α) ↔ (∀ (_ : α), 0 = 0))
set_option egg.eraseForallDomains true in
example : True = True := by
  sorry -- egg [h]
