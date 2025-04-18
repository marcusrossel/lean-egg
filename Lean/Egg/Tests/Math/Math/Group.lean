import Mathlib
import Egg

set_option egg.genTcProjRws false -- TODO: Things still work if we keep this, but it seems not to be necessary.

attribute [egg group] mul_assoc one_mul mul_one inv_mul_cancel mul_inv_cancel

namespace Test

variable [Group G] {a b : G}

theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by egg group

theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by egg group

theorem inv_one : (1 : G)⁻¹ = 1 := by egg
  group using 1 * (1 : G)⁻¹

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  egg group calc
    _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹
    _ = _

theorem inv_inv : a⁻¹⁻¹ = a := by
  egg group calc
    _ = a⁻¹⁻¹ * (a⁻¹ * a)
    _ = _

theorem inv_mul' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  egg group using b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹

theorem inv_inv' : a⁻¹⁻¹ = a := by
  egg group using a⁻¹⁻¹ * a⁻¹ * a
