import Mathlib
import Egg

set_option egg.tcProjs false -- TODO: Things still work if we keep this, but it seems not to be necessary.

-- NOTE: We're only covering the multiplicative (not the additive) versions of structures.

attribute [egg semigroup] Semigroup.mul_assoc

attribute [egg comm_magma] CommMagma.mul_comm

egg_basket comm_semigroup extends semigroup, comm_magma

-- NOTE: Skipped cancelation definitions around lines 200-280

attribute [egg mul_one] MulOneClass.one_mul MulOneClass.mul_one MulOneClass.ext

-- NOTE: Skipped power definitions around lines 330-550.

egg_basket monoid extends semigroup, mul_one with Monoid.npow_zero, Monoid.npow_succ, npow_eq_pow

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

-- NOTE: We can't use `mul_one` to rewrite from `b` to `b * 1` as that requires the LHS to be just a
--       lone mvar. Thus, we have to specify the guide term `b * 1`.
example (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  egg +monoid [*] using b * 1

/- Previous -/ attribute [egg monoid] left_inv_eq_right_inv

end Monoid

-- NOTE: Skipped power theorems around lines 590-650.

egg_basket comm_monoid extends monoid, comm_semigroup

-- NOTE: Skipped cancel and involutive definitions around lines 660-760.

egg_basket div_inv_monoid extends monoid with DivInvMonoid.div_eq_mul_inv

-- NOTE: Skipped power axioms and theorems around lines 830-940.

section DivInvMonoid
variable [DivInvMonoid G]

attribute [egg div_inv_monoid] div_eq_mul_inv

example (x : G) : x⁻¹ = 1 / x := by
  egg +div_inv_monoid

/- Previous -/ attribute [egg div_inv_monoid] inv_eq_one_div

example (a b c : G) : a * b / c = a * (b / c) := by
  egg +div_inv_monoid

/- Previous -/ attribute [egg div_inv_monoid] mul_div_assoc

example (a : G) : 1 / a = a⁻¹ := by
  egg +div_inv_monoid

/- Previous -/ attribute [egg div_inv_monoid] one_div

end DivInvMonoid

-- NOTE: Skipped power theorems, `InvOneClass`, and `DivisionMonoid` around lines 960-1050.

egg_basket group extends div_inv_monoid with Group.inv_mul_cancel

section Group
variable [Group G] {a b : G}

attribute [egg group] inv_mul_cancel

-- TODO: Make this theorem private (as it is in its source file).
--       Adding private theorems to egg baskets becomes problematic when using the basket in other
--       files. In that case elaboration fails, and we get:
--       "egg requires premises to be (proofs of) propositions or (non-propositional) definitions"
--       Add support for local egg theorems.
theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

/- Previous -/ attribute [egg group] inv_eq_of_mul

example (a : G) : a * a⁻¹ = 1 := by
  egg +group using a⁻¹ * a

/- Previous -/ attribute [egg group] mul_inv_cancel

-- theorem div_self'
example (a : G) : a / a = 1 := by
  egg +group

/- Previous -/ attribute [egg group] div_self'

example (a b : G) : a⁻¹ * (a * b) = b := by
  egg +group

/- Previous -/ attribute [egg group] inv_mul_cancel_left

example (a b : G) : a * (a⁻¹ * b) = b := by
  egg +group

/- Previous -/ attribute [egg group] mul_inv_cancel_left

example (a b : G) : a * b * b⁻¹ = a := by
  egg +group

/- Previous -/ attribute [egg group] mul_inv_cancel_right

-- theorem mul_div_cancel_right
example (a b : G) : a * b / b = a := by
  egg +group

/- Previous -/ attribute [egg group] mul_div_cancel_right

example (a b : G) : a * b⁻¹ * b = a := by
  egg +group

/- Previous -/ attribute [egg group] inv_mul_cancel_right

example (a b : G) : a / b * b = a := by
  egg +group

/- Previous -/ attribute [egg group] div_mul_cancel

-- TODO: Group.toDivisionMonoid
--
-- inv_inv: egg group using a⁻¹⁻¹ * a⁻¹ * a
-- mul_inv_rev: egg group using b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹
instance (priority := 100) : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (inv_mul_cancel a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- TODO: Group.toCancelMonoid
instance (priority := 100) : CancelMonoid G :=
  { ‹Group G› with
    mul_right_cancel := fun a b c h ↦ by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]
    mul_left_cancel := fun a b c h ↦ by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left] }

end Group

egg_basket comm_group extends group, comm_monoid

section CommGroup
variable [CommGroup G]

example (a b : G) : a⁻¹ * b * a = b := by
  egg +comm_group

/- Previous -/ attribute [egg comm_group] inv_mul_cancel_comm

example (a b : G) : a * b * a⁻¹ = b := by
  egg +comm_group

/- Previous -/ attribute [egg comm_group] mul_inv_cancel_comm

example (a b : G) : a⁻¹ * (b * a) = b := by
  egg +comm_group

/- Previous -/ attribute [egg comm_group] inv_mul_cancel_comm_assoc

example (a b : G) : a * (b * a⁻¹) = b := by
  egg +comm_group

/- Previous -/ attribute [egg comm_group] mul_inv_cancel_comm_assoc

end CommGroup
