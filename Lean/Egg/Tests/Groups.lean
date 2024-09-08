import Egg

class One (α) where one : α

instance [One α] : OfNat α 1 where ofNat := One.one

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Group (α) extends One α, Inv α, Mul α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group G] {a b : G}

open Group Egg.Guides Egg.Config.Modifier in
macro "group" mod:egg_cfg_mod base:(egg_base)? guides:(egg_guides)? : tactic => `(tactic|
  egg $mod [mul_assoc, one_mul, mul_one, inv_mul_self, mul_inv_self] $[$base]? $[$guides]?
)

theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by group

theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by group

theorem inv_one : (1 : G)⁻¹ = 1 := by group

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  calc _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹ := by group
       _ = _                               := by group

theorem inv_inv : a⁻¹⁻¹ = a := by
  calc _ = a⁻¹⁻¹ * (a⁻¹ * a) := by group
       _ = _                 := by group

set_option egg.timeLimit 3 in
theorem inv_mul' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group using b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹

set_option egg.timeLimit 7 in
theorem inv_mul'' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group using a⁻¹ * (a * b) * (a * b)⁻¹

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
set_option egg.timeLimit 10 in
theorem inv_mul''' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group using (a * b) * (a * b)⁻¹

theorem inv_inv' : a⁻¹⁻¹ = a := by
  group using a⁻¹ * a
