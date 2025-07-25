import Egg

class Group (α) extends Mul α, One α, Inv α where
  mul_assoc    (a b c : α) : (a * b) * c = a * (b * c)
  one_mul      (a : α)     : 1 * a = a
  mul_one      (a : α)     : a * 1 = a
  inv_mul_self (a : α)     : a⁻¹ * a = 1
  mul_inv_self (a : α)     : a * a⁻¹ = 1

variable [Group α] (a b x y : α)

attribute [egg group] Group.mul_assoc
attribute [egg group] Group.one_mul
attribute [egg group] Group.mul_one
attribute [egg group] Group.inv_mul_self
attribute [egg group] Group.mul_inv_self

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example : a⁻¹ * (a * b) = b := by egg

/-- info: Group.inv_mul_self, Group.mul_assoc, Group.mul_inv_self, Group.mul_one, Group.one_mul -/
#guard_msgs in #egg_basket group

@[egg group]
theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by egg +group

/--
info: inv_mul_cancel_left, Group.inv_mul_self, Group.mul_assoc, Group.mul_inv_self, Group.mul_one, Group.one_mul
-/
#guard_msgs in #egg_basket group

@[egg group]
theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by egg +group

/--
info: inv_mul_cancel_left, mul_inv_cancel_left, Group.inv_mul_self, Group.mul_assoc, Group.mul_inv_self, Group.mul_one, Group.one_mul
-/
#guard_msgs in #egg_basket group
