import Mathlib.Algebra.Lie.Basic
import Egg

set_option egg.genNestedSplits false
set_option egg.genTcProjRws false -- TODO: Things still work if we keep this, but it seems not to be necessary.
set_option egg.genGroundEqs false -- TODO: Things still work if we keep this, but it seems not to be necessary.

universe u v w w₁ w₂

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

variable {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [LieRing L₁] [LieAlgebra R L₁]
variable [LieRing L₂] [LieAlgebra R L₂]
variable [LieRing L₃] [LieAlgebra R L₃]

example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← add_lie]
  simp only [neg_add_cancel, zero_lie]

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← lie_add]
  simp only [neg_add_cancel, lie_zero]

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  simp only [sub_eq_add_neg, add_lie, neg_lie]

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  simp only [sub_eq_add_neg, lie_add, lie_neg]

example : ⁅-x, m⁆ - -⁅x, m⁆ = 0 := by
  egg [sub_eq_zero, neg_lie]

example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  egg [neg_add_cancel, zero_lie, sub_eq_zero, sub_neg_eq_add, add_lie]

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  egg [sub_eq_zero, sub_neg_eq_add, lie_add, neg_add_cancel, lie_zero]

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  egg [sub_eq_add_neg, add_lie, neg_lie]

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  egg [sub_eq_add_neg, lie_add, lie_neg]

-- lie_skew
example : -⁅y, x⁆ = ⁅x, y⁆ := by
  egg [neg_eq_iff_add_eq_zero, lie_add, add_lie, lie_self, zero_add, add_zero]
    using ⁅x + y, x⁆ + ⁅x + y, y⁆

namespace LieHom

-- inverse
example (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intros x y
      egg calc [h₂ x, h₂ y, map_lie, h₁ _]
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆
        _ = g (f ⁅g x, g y⁆)
        _ = ⁅g x, g y⁆
  }
