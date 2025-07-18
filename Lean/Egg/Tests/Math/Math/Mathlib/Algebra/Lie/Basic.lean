import Mathlib.Algebra.Lie.Basic
import Egg

set_option grind.warning false
set_option egg.tcProjs false -- TODO: Things still work if we keep this, but it seems not to be necessary.
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

example : -⁅y, x⁆ = ⁅x, y⁆ := by
  egg +lie using ⁅x + y, x⁆ + ⁅x + y, y⁆

example : ⁅x, y⁆ = -⁅y, x⁆ := by
  have h1 : 0 = ⁅x, y⁆ + ⁅y, x⁆ := by calc
    _ = ⁅x + y, x + y⁆ := by                    grind [add_lie, lie_add, smul_lie, lie_smul, lie_zero, zero_lie, lie_self, add_zero, zero_add]
    _ = ⁅x, x⁆ + ⁅x, y⁆ + ⁅y, x⁆ + ⁅y, y⁆ := by grind [add_lie, lie_add, smul_lie, lie_smul, lie_zero, zero_lie, lie_self, add_zero, zero_add]
    _ = ⁅x, y⁆ + ⁅y, x⁆ := by                   grind [add_lie, lie_add, smul_lie, lie_smul, lie_zero, zero_lie, lie_self, add_zero, zero_add]
  try grind  [sub_eq_zero, sub_neg_eq_add]
  egg [sub_eq_zero, sub_neg_eq_add, h1]

example : ⁅x, y⁆ = -⁅y, x⁆ := by
  have h : 0 = ⁅x, y⁆ + ⁅y, x⁆ := by
    egg +lie calc
      _ = ⁅x + y, x + y⁆
      _ = ⁅x, x⁆ + ⁅x, y⁆ + ⁅y, x⁆ + ⁅y, y⁆
      _ = ⁅x, y⁆ + ⁅y, x⁆
  egg +lie [h]

/- Previous -/ attribute [egg lie] lie_skew

-- lieAlgebraSelfModule
example : LieModule R L L where
  smul_lie := by egg +lie
  lie_smul := by egg +lie

-- NOTE: This example relies on `egg.derivedGuides`, because it needs the term `⁅-x, m⁆ = -⁅x, m⁆`
--       in the e-graph in order to apply `sub_eq_zero`. Note that even though the LHS `⁅-x, m⁆` and
--       RHS `-⁅x, m⁆` of the goal are automatically added to the e-graph, this does not mean that
--       `eq`-node is created for them, as they do not live in the same e-class (a priori).
-- NOTE: This example relies on `egg.goalTypeSpec`, because the encoding of `sub_eq_zero` erases the
--       type `?G` in the RHS equality, which makes the backward direction unapplicable by default.
example : ⁅-x, m⁆ = -⁅x, m⁆ := by
  egg +lie

/- Previous -/ attribute [egg lie] neg_lie

example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  egg +lie

/- Previous -/ attribute [egg lie] lie_neg

/--
error: `grind` failed
case grind
R : Type u
L : Type v
M : Type w
N : Type w₁
inst : CommRing R
inst_1 : LieRing L
inst_2 : LieAlgebra R L
inst_3 : AddCommGroup M
inst_4 : Module R M
inst_5 : LieRingModule L M
inst_6 : LieModule R L M
inst_7 : AddCommGroup N
inst_8 : Module R N
inst_9 : LieRingModule L N
inst_10 : LieModule R L N
t : R
x y z : L
m n : M
h : ¬⁅x, -m⁆ = -⁅x, m⁆
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] LieModule R L M
    [prop] LieModule R L N
    [prop] ¬⁅x, -m⁆ = -⁅x, m⁆
  [eqc] True propositions
    [prop] LieModule R L M
    [prop] LieModule R L N
  [eqc] False propositions
    [prop] ⁅x, -m⁆ = -⁅x, m⁆
  [ematch] E-matching patterns
    [thm] neg_add_cancel: [@HAdd.hAdd #2 _ _ _ (@Neg.neg _ _ #0) #0]
    [thm] lie_zero: [@Bracket.bracket #5 #4 _ #0 (@OfNat.ofNat _ `[0] _)]
    [thm] sub_eq_zero: [@HSub.hSub #3 _ _ _ #1 #0]
    [thm] sub_neg_eq_add: [@HSub.hSub #3 _ _ _ #1 (@Neg.neg _ _ #0)]
    [thm] lie_add: [@Bracket.bracket #7 #6 _ #2 (@HAdd.hAdd _ _ _ _ #1 #0)]
-/
#guard_msgs in
example : ⁅x, -m⁆ = -⁅x, m⁆ := by
  grind [neg_add_cancel, lie_zero, ← sub_eq_zero, sub_neg_eq_add, ← lie_add]

example : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by
  egg +lie

/- Previous -/ attribute [egg lie] sub_lie

example : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by
  egg +lie

/- Previous -/ attribute [egg lie] lie_sub

attribute [egg lie] nsmul_lie lie_nsmul zsmul_lie lie_zsmul

example : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by
  egg +lie

/- Previous -/ attribute [egg lie] lie_lie

example : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  egg +lie

/- Previous -/ attribute [egg lie] lie_jacobi

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

attribute [egg lie] LieHom.lie_apply

-- TODO: LinearMap.instLieModule
example : LieModule R L (M →ₗ[R] N) where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, LinearMap.smul_apply, LinearMap.map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, LinearMap.smul_apply, LieHom.lie_apply, lie_smul]

attribute [egg lie] Module.Dual.lie_apply sum_lie lie_sum sum_lie_sum

end BasicProperties
