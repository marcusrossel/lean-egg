import Mathlib.Algebra.Lie.Basic
import Math.Comparisons.Simp

set_option grind.warning false

attribute [grind, lie_simp] neg_eq_iff_add_eq_zero zero_add add_zero smul_neg sub_eq_zero neg_neg
                  sub_neg_eq_add neg_add_cancel sub_eq_add_neg add_sub_cancel_right
                  smul_sub

attribute [grind, lie_simp] LieRing.add_lie LieRing.lie_add LieRing.lie_self LieRing.leibniz_lie

-- NOTE: Grind can't construct a pattern for these:
attribute [grind, lie_simp] LieAlgebra.lie_smul LieRingModule.add_lie LieRingModule.lie_add
                  LieRingModule.leibniz_lie

attribute [grind, lie_simp] LieModule.smul_lie LieModule.lie_smul

attribute [grind, lie_simp] leibniz_lie lie_swap_lie

attribute [grind, lie_simp] add_lie lie_add smul_lie lie_smul lie_zero zero_lie lie_self

section BasicProperties

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

example : ⁅x, y⁆ = -⁅y, x⁆ := by
  have : 0 = ⁅x, y⁆ + ⁅y, x⁆ := by calc
    _ = ⁅x + y, x + y⁆ :=                    by grind
    _ = ⁅x, x⁆ + ⁅x, y⁆ + ⁅y, x⁆ + ⁅y, y⁆ := by grind
    _ = ⁅x, y⁆ + ⁅y, x⁆ :=                   by grind
  fail_if_success grind
  sorry

example : ⁅x, y⁆ = -⁅y, x⁆ := by
  have : 0 = ⁅x, y⁆ + ⁅y, x⁆ := by calc
    _ = ⁅x + y, x + y⁆ :=                    by simp only [lie_simp, *]
    _ = ⁅x, x⁆ + ⁅x, y⁆ + ⁅y, x⁆ + ⁅y, y⁆ := by simp only [lie_simp, *]; sorry
    _ = ⁅x, y⁆ + ⁅y, x⁆ :=                   by simp only [lie_simp, *]
  fail_if_success simp only [lie_simp, *]
  sorry

/- Previous -/ attribute [grind, lie_simp] lie_skew

-- lieAlgebraSelfModule
example : LieModule R L L where
  smul_lie := by grind
  lie_smul := by grind

example : LieModule R L L where
  smul_lie := by simp only [lie_simp, *]; sorry
  lie_smul := by simp only [lie_simp, *]; sorry

-- NOTE: This example relies on `egg.derivedGuides`, because it needs the term `⁅-x, m⁆ = -⁅x, m⁆`
--       in the e-graph in order to apply `sub_eq_zero`. Note that even though the LHS `⁅-x, m⁆` and
--       RHS `-⁅x, m⁆` of the goal are automatically added to the e-graph, this does not mean that
--       `eq`-node is created for them, as they do not live in the same e-class (a priori).
-- NOTE: This example relies on `egg.goalTypeSpec`, because the encoding of `sub_eq_zero` erases the
--       type `?G` in the RHS equality, which makes the backward direction unapplicable by default.
example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  fail_if_success grind
  fail_if_success simp only [lie_simp, *]
  sorry

/- Previous -/ attribute [grind, lie_simp] neg_lie

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  fail_if_success grind
  fail_if_success simp only [lie_simp, *]
  sorry

/- Previous -/ attribute [grind, lie_simp] lie_neg

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  grind

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  simp only [lie_simp, *]

/- Previous -/ attribute [grind, lie_simp] sub_lie

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  grind

/- Previous -/ attribute [grind, lie_simp] lie_sub

attribute [grind, lie_simp] nsmul_lie lie_nsmul zsmul_lie lie_zsmul

example : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by
  grind

/- Previous -/ attribute [grind, lie_simp] lie_lie

example : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  grind

/- Previous -/ attribute [grind, lie_simp] lie_jacobi

-- TODO: LinearMap.instLieRingModule
example : LieRingModule L (M →ₗ[R] N) where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, LinearMap.map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, LinearMap.map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.map_add]
    abel
  lie_add x f g := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, lie_add, LinearMap.add_apply]
    abel
  leibniz_lie x y f := by
    ext n
    simp only [lie_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_sub, LinearMap.add_apply,
      lie_sub]
    abel

/- Previous -/ attribute [grind, lie_simp] LieHom.lie_apply

-- TODO: LinearMap.instLieModule
example : LieModule R L (M →ₗ[R] N) where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, LinearMap.smul_apply, LinearMap.map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, LinearMap.smul_apply, LieHom.lie_apply, lie_smul]

/- Previous -/ attribute [grind, lie_simp] Module.Dual.lie_apply sum_lie lie_sum sum_lie_sum

end BasicProperties
