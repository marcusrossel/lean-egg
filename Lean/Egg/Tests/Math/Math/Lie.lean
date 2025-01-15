import Mathlib.Algebra.Lie.Basic
import Egg

universe u v w w₁ w₂

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

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
  egg [neg_add_cancel, zero_lie, sub_neg_eq_add, add_lie]

set_option egg.timeLimit 10
set_option egg.genNestedSplits false

example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  egg [neg_add_cancel, zero_lie, sub_eq_zero, sub_neg_eq_add, add_lie]

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  egg [sub_eq_zero, sub_neg_eq_add, lie_add, neg_add_cancel, lie_zero]

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  egg [sub_eq_add_neg, add_lie, neg_lie]

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  egg [sub_eq_add_neg, lie_add, lie_neg]
