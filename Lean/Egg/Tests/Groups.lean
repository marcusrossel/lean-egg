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

theorem inv_add_cancel_left : -a + (a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem add_inv_cancel_left : a + (-a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

-- TODO: This test case should be fixed by typeclass specialization.

theorem zero_inv : -(0 : G) = 0 := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

-- TODO: The test cases below should be fixed by explosion.

theorem inv_add : -(a + b) = -b + -a := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_inv : -(-a) = a := by
  sorry -- egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]
