import Egg

macro "#basket" key:ident : command => `(
  #eval show Lean.Meta.MetaM _ from Egg.extension.getBasket $(Lean.quote key.getId)
)

class One (α) where one : α
instance [One α] : OfNat α 1 where ofNat := One.one

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

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

/--
info: #[`Group.mul_assoc, `Group.one_mul, `Group.mul_one, `Group.inv_mul_self, `Group.mul_inv_self]
-/
#guard_msgs in #basket group

@[egg group]
theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by egg group

/--
info: #[`Group.mul_assoc, `Group.one_mul, `Group.mul_one, `Group.inv_mul_self, `Group.mul_inv_self, `inv_mul_cancel_left]
-/
#guard_msgs in #basket group

@[egg group]
theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by egg group

/--
info: #[`Group.mul_assoc, `Group.one_mul, `Group.mul_one, `Group.inv_mul_self, `Group.mul_inv_self, `inv_mul_cancel_left,
  `mul_inv_cancel_left]
-/
#guard_msgs in #basket group
