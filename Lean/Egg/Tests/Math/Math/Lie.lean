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

def f : Prop := sorry
theorem h : (⁅-x, m⁆ - -⁅x, m⁆ = 0) ↔ f := sorry

-- PROBLEM: The fact that the type `M` appears in the subtraction of `?a - ?b = 0` but not in the
--          equality `?a = ?b` causes `sub_eq_zero` to not be applicable in both directions by
--          default. The nested split in the `←` direction *is* bidirectional, but contains `M` as
--          an unbound mvar in the condition `AddGroup ?m`. This should be resolved by type class
--          specialization. Why is it not?
set_option trace.egg true in
example : (⁅-x, m⁆ = -⁅x, m⁆) ↔ f := by
  egg [sub_eq_zero]

set_option trace.egg true in
example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  egg [neg_add_cancel, zero_lie, sub_eq_zero, sub_neg_eq_add, add_lie] -- using ⁅-x, m⁆ - -⁅x, m⁆ = 0

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  egg [sub_eq_zero, sub_neg_eq_add, lie_add, neg_add_cancel, lie_zero] using ⁅x, -m⁆ - -⁅x, m⁆ = 0

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  egg [sub_eq_add_neg, add_lie, neg_lie]

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  egg [sub_eq_add_neg, lie_add, lie_neg]
