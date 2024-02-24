import Egg

class Group (α) where
  zero          : α
  neg           : α → α
  add           : α → α → α
  add_assoc     : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add      : ∀ a, add zero a = a
  add_zero      : ∀ a, add a zero = a
  add_left_inv  : ∀ a, add (neg a) a = zero
  add_right_inv : ∀ a, add a (neg a) = zero

open Group

instance [Group α] : Neg α where neg := neg
instance [Group α] : Add α where add := add
instance [Group α] : OfNat α 0 where ofNat := zero

variable [g : Group G] {a b c : G}

-- NOTE: Using `@add_assoc` etc, produces `.proj` expressions.

-- BUG: since switching proof reconstruction
--
-- This looks like the same problem we ran into here:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20TermCongr.20isDefEq
-- Though it might also be a problem with mvars which have already been assigned and are trying to
-- be reassigned.
set_option trace.egg true in
set_option pp.all true in
theorem inv_add_cancel_left : -a + (a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

-- BUG: since switching proof reconstruction
theorem add_inv_cancel_left : a + (-a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

-- TODO: The test cases below should be fixed by explosion.

theorem inv_add : -(a + b) = -b + -a := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

-- Proof:
--   simp [Neg.neg, OfNat.ofNat]
--   rw [←add_zero (a := neg zero)]
--   rw [add_left_inv]
theorem zero_inv : -(0 : G) = 0 := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_inv : -(-a) = a := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]
