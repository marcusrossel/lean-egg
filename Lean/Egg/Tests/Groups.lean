import Egg

class Zero (α) where zero : α
instance [Zero α] : OfNat α 0 where ofNat := Zero.zero

class Group (α) extends Zero α, Neg α, Add α where
  add_assoc     (a b c : α) : (a + b) + c = a + (b + c)
  zero_add      (a : α)     : 0 + a = a
  add_zero      (a : α)     : a + 0 = a
  add_left_neg  (a : α)     : -a + a = 0
  add_right_neg (a : α)     : a + -a = 0

variable [Group G] {a b : G}

open Group Egg.Guides Egg.Config.Modifier in
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
  group using -a + (a + b) + -(a + b)

theorem inv_inv' : -(-a) = a := by
  group using -a + a
