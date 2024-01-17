import Egg

-- TODO: This set of test cases seems to demonstrate that `typeTags ≠ .none` is way too slow or
--       doesn't work.

def G : Type := sorry
def zero : G := sorry
def neg : G → G := sorry
def add : G → G → G := sorry

instance : Neg G where neg := neg
instance : Add G where add := add
instance : OfNat G 0 where ofNat := zero

-- TODO: If you change this to be implicit arguments, the examples below fail.
variable {a b c : G}

theorem add_assoc     : (a + b) + c = a + (b + c) := by sorry
theorem zero_add      : 0 + a = a                 := by sorry
theorem add_zero      : a + 0 = a                 := by sorry
theorem add_left_inv  : -a + a = 0                := by sorry
theorem add_right_inv : a + -a = 0                := by sorry

set_option trace.egg.reconstruction true
-- TODO: Do the following reconstructions fail, because the position of the rewrite is wrong?

theorem inv_add_cancel_left : -a + (a + b) = b := by
  -- rw (config := { occs := .pos [1]}) [← @add_assoc (-a) a b]
  -- rw (config := { occs := .pos [1]}) [@add_left_inv a]
  -- rw (config := { occs := .pos [1]}) [← @zero_add 0]
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem add_inv_cancel_left : a + (-a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_add : -(a + b) = -b + -a := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem zero_inv : -(0 : G) = 0 := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_inv : -(-a) = a := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]
