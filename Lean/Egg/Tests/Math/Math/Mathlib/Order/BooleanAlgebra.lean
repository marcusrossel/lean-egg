import Egg
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

set_option egg.explLengthLimit 250

-- SemilatticeSup
attribute [egg slattice_sup] sup_idem sup_comm sup_assoc sup_left_right_swap sup_left_idem
                             sup_right_idem sup_left_comm sup_right_comm sup_sup_sup_comm
                             sup_sup_distrib_left sup_sup_distrib_right sup_congr_left
                             sup_congr_right

-- SemilatticeInf
attribute [egg slattice_inf] inf_of_le_left inf_of_le_right inf_idem inf_comm inf_assoc
                             inf_left_right_swap inf_left_idem inf_right_idem inf_left_comm
                             inf_right_comm inf_inf_inf_comm inf_inf_distrib_left
                             inf_inf_distrib_right inf_congr_left inf_congr_right

-- Lattice
egg_basket lattice extends slattice_sup, slattice_inf with
  inf_sup_self, sup_inf_self

-- DistribLattice
egg_basket distrib_lattice extends lattice with
  sup_inf_left, sup_inf_right, inf_sup_left, inf_sup_right, eq_of_inf_eq_sup_eq

-- GeneralizedBooleanAlgebra
egg_basket bool extends distrib_lattice with
  sup_inf_sdiff, inf_inf_sdiff

variable [GeneralizedBooleanAlgebra α] {x y z : α}
example (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  egg +bool [sup_inf_sdiff x y, inf_inf_sdiff x y, i, s]

/- Previous -/ attribute [egg bool] sdiff_unique

theorem sdiff_le' : x \ y ≤ x := by
  egg +bool [le_sup_right] using x ⊓ y ⊔ x \ y

/- Previous -/ attribute [egg bool] sdiff_le'

theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x := by
  egg +bool calc
    _ = y \ x ⊔ (x ⊔ x ⊓ y)
    _ = y ⊓ x ⊔ y \ x ⊔ x
    _ = y ⊔ x

-- TODO: I think this might produce a loop in proof reconstruction.
example : y \ x ⊔ x = y ⊔ x := by
  sorry -- egg +bool using y \ x ⊔ (x ⊔ x ⊓ y)

/- Previous -/ attribute [egg bool] sdiff_sup_self'

attribute [egg bool] inf_sdiff_right

example : x \ y ⊓ y \ x = ⊥ := by
  egg +bool

/- Previous -/ attribute [egg bool] sdiff_inf_sdiff

example : x ⊓ y \ x = ⊥ := by
  egg +bool using x ⊓ y ⊔ x \ y

/- Previous -/ attribute [egg bool] inf_sdiff_self_right

example : y \ (x ⊔ z) = y \ x ⊓ y \ z := by
  apply sdiff_unique
  · egg +bool using (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z))
  · egg +bool using y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z)

/- Previous -/ attribute [egg bool] sdiff_sup

example : x \ y = x ↔ Disjoint y x := by
  egg +bool [sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, disjoint_iff] using x ⊓ ⊥

/- Previous -/ attribute [egg bool] sdiff_eq_self_iff_disjoint

example (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  egg +bool [h, inf_eq_right, hx]

/- Previous -/ attribute [egg bool] sdiff_lt

example : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  egg +bool

/- Previous -/ attribute [egg bool] sup_inf_inf_sdiff

example : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · egg +bool using x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y)
  · egg +bool [inf_sdiff_left] using x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y

/- Previous -/ attribute [egg bool] sdiff_sdiff_right

example : x \ (y \ z) = x \ y ⊔ x ⊓ z := by
  egg +bool

/- Previous -/ attribute [egg bool] sdiff_sdiff_right'

example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  egg +bool using z \ x ⊔ z ⊓ x ⊓ y

/- Previous -/ attribute [egg bool] sdiff_sdiff_sup_sdiff

example : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by
  egg +bool

/- Previous -/ attribute [egg bool] sdiff_sdiff_sup_sdiff'

example : (x ⊓ y) \ z = x \ z ⊓ y \ z := by
  apply sdiff_unique <;> egg +bool using (y ⊓ (x ⊓ (x ⊔ z)) ⊔ x \ z) ⊓ (x ⊓ y ⊓ z ⊔ y \ z)

/- Previous -/ attribute [egg bool] inf_sdiff

example (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z := by
  apply sdiff_unique <;> egg +bool [inf_bot_eq]

/- Previous -/ attribute [egg bool] inf_sdiff_assoc

example : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y := by
  egg +bool

/- Previous -/ attribute [egg bool] sup_eq_sdiff_sup_sdiff_sup_inf
