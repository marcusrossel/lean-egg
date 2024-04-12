import Egg
import Lean

class Group (α) where
  zero          : α
  neg           : α → α
  add           : α → α → α
  add_assoc     : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add      : ∀ a, add zero a = a
  add_zero      : ∀ a, add a zero = a
  add_left_neg  : ∀ a, add (neg a) a = zero
  add_right_neg : ∀ a, add a (neg a) = zero

open Group

instance [Group α] : Neg α where neg := neg
instance [Group α] : Add α where add := add
instance [Group α] : OfNat α 0 where ofNat := zero

variable [Group G] {a b : G}

open Egg.Guides Egg.Config.Modifier in
macro "group" mod:egg_cfg_mod base:(egg_base)? guides:(egg_guides)? : tactic => `(tactic|
  egg $mod [add_assoc, zero_add, add_zero, add_left_neg, add_right_neg] $[$base]? $[$guides]?
)

theorem neg_add_cancel_left : -a + (a + b) = b := by group

theorem add_neg_cancel_left : a + (-a + b) = b := by group

theorem neg_zero : -(0 : G) = 0 := by group

theorem neg_add : -(a + b) = -b + -a := by
  calc _ = -b + -a + (a + b) + -(a + b) := by group
       _ = _                            := by group

theorem inv_inv : -(-a) = a := by
  calc _ = -(-a) + (-a + a) := by group
       _ = _                := by group

theorem neg_add' : -(a + b) = -b + -a := by
  group via -b + -a + (a + b) + -(a + b)

-- BUG: Try adding a hypothesis. This should cause the backend to crash.
theorem inv_inv' : -(-a) = a := by
  group via -(-a) + (-a + a)
