import Mathlib
import Egg

set_option egg.timeLimit 10

attribute [egg] mul_assoc one_mul mul_one inv_mul_self mul_inv_self

namespace Test

variable [Group G] {a b : G}

theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by egg!

theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by egg!

theorem inv_one : (1 : G)⁻¹ = 1 := by egg!

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  egg! calc _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹
            _ = _

theorem inv_inv : a⁻¹⁻¹ = a := by
  egg! calc _ = a⁻¹⁻¹ * (a⁻¹ * a)
            _ = _

theorem inv_mul'' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  egg! using a⁻¹ * (a * b) * (a * b)⁻¹

theorem inv_inv' : a⁻¹⁻¹ = a := by
  egg! using a⁻¹ * a
