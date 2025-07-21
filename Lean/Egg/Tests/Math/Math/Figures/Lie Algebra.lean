import Mathlib.Algebra.Lie.Basic
import Egg

set_option egg.timeLimit 10

attribute [egg lie_external] neg_eq_iff_add_eq_zero zero_add add_zero smul_neg sub_eq_zero neg_neg
                             sub_neg_eq_add neg_add_cancel sub_eq_add_neg add_sub_cancel_right
                             smul_sub

-- TODO: extends AddCommGroup
attribute [egg lie_ring] LieRing.add_lie LieRing.lie_add LieRing.lie_self LieRing.leibniz_lie

 -- TODO: extends CommRing and Module
egg_basket lie_alg extends lie_ring with LieAlgebra.lie_smul

egg_basket lie_ring_mod extends lie_ring, lie_alg with
  LieRingModule.add_lie, LieRingModule.lie_add, LieRingModule.leibniz_lie

egg_basket lie_mod extends lie_ring, lie_alg, lie_ring_mod with
  LieModule.smul_lie, LieModule.lie_smul

attribute [egg lie_tower] leibniz_lie lie_swap_lie

egg_basket lie extends lie_ring_mod, lie_tower, lie_external with
  add_lie, lie_add, smul_lie, lie_smul, lie_zero, zero_lie, lie_self

section BasicProperties

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

theorem L1' : ⁅x, y⁆ = -⁅y, x⁆ := by
  have h := by
    egg +lie calc
      0 = ⁅x + y, x + y⁆
      _ = ⁅x, x⁆ + ⁅x, y⁆ + ⁅y, x⁆ + ⁅y, y⁆
      _ = ⁅x, y⁆ + ⁅y, x⁆
  egg +lie [h]

example /- L1' -/ : ⁅x, y⁆ = -⁅y, x⁆ := by
  egg +lie using ⁅x + y, x⁆ + ⁅x + y, y⁆

/- Previous -/ attribute [egg lie] lie_skew

example /- neg_lie -/ : ⁅-x, m⁆ = -⁅x, m⁆ := by
  egg +lie
