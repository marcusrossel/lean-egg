import Egg

class One (α) where one : α
instance [One α] : OfNat α 1 where ofNat := One.one

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

class Group (α) extends Mul α, One α, Inv α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group α] (a b x y : α)

attribute [egg] Group.mul_assoc
attribute [egg] Group.one_mul
attribute [egg] Group.mul_one
attribute [egg] Group.inv_mul_self
attribute [egg] Group.mul_inv_self

/-- info: egg set: [Group.mul_assoc, Group.one_mul, Group.mul_one, Group.inv_mul_self, Group.mul_inv_self] -/
 #guard_msgs(info) in
#show_egg_set

@[egg]
theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  egg

/-- info: egg set: [Group.mul_assoc, Group.one_mul, Group.mul_one, Group.inv_mul_self, Group.mul_inv_self, inv_mul_cancel_left] -/
 #guard_msgs(info) in
#show_egg_set

@[egg]
theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b :=  by
  egg

-- TODO: should egg (or a version of egg) do the intros automatically to get an eq goal?
@[egg]
theorem mul_eq_de_eq_inv_mul : x = a⁻¹ * y → a * x = y := by
 intros h
 egg [h]
