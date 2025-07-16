import Mathlib.Order.BooleanAlgebra
import Math.Comparisons.Simp

set_option grind.warning false

-- SemilatticeSup
attribute [grind, bool_simp] sup_idem sup_comm sup_assoc sup_left_right_swap sup_left_idem
                  sup_right_idem sup_left_comm sup_right_comm sup_sup_sup_comm
                  sup_sup_distrib_left sup_sup_distrib_right sup_congr_left
                  sup_congr_right

-- SemilatticeInf
attribute [grind, bool_simp] inf_of_le_left inf_of_le_right inf_idem inf_comm inf_assoc
                  inf_left_right_swap inf_left_idem inf_right_idem inf_left_comm
                  inf_right_comm inf_inf_inf_comm inf_inf_distrib_left
                  inf_inf_distrib_right inf_congr_left inf_congr_right

-- Lattice
attribute [grind, bool_simp] inf_sup_self sup_inf_self

-- DistribLattice
attribute [grind, bool_simp] sup_inf_left sup_inf_right inf_sup_left inf_sup_right eq_of_inf_eq_sup_eq

-- GeneralizedBooleanAlgebra
attribute [grind, bool_simp] sup_inf_sdiff inf_inf_sdiff

variable [GeneralizedBooleanAlgebra α] {x y z : α}

example (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  fail_if_success grind [sup_inf_sdiff, inf_inf_sdiff, i, s]
  fail_if_success simp only [*, bool_simp, sup_inf_sdiff, inf_inf_sdiff, i, s]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_unique

theorem sdiff_le' : x \ y ≤ x := by
  fail_if_success grind [le_sup_right]
  fail_if_success simp only [*, bool_simp, le_sup_right]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_le'

theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x := by
  calc
  y \ x ⊔ x
  _ = y \ x ⊔ (x ⊔ x ⊓ y) := by grind
  _ = y ⊓ x ⊔ y \ x ⊔ x   := by grind
  _ = y ⊔ x               := by grind

example : y \ x ⊔ x = y ⊔ x := by
  calc
  y \ x ⊔ x
  _ = y \ x ⊔ (x ⊔ x ⊓ y) := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = y ⊓ x ⊔ y \ x ⊔ x   := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = y ⊔ x               := by (fail_if_success simp only [*, bool_simp]); sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sup_self'

example : x \ y ⊓ y \ x = ⊥ := by
  fail_if_success grind [inf_of_le_right, sdiff_le']
  fail_if_success simp only [*, bool_simp, inf_of_le_right, sdiff_le']
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_inf_sdiff

example : x ⊓ y \ x = ⊥ := by
  fail_if_success grind
  fail_if_success simp only [*, bool_simp]
  sorry

/- Previous -/ attribute [grind, bool_simp] inf_sdiff_self_right

example : y \ (x ⊔ z) = y \ x ⊓ y \ z := by
  apply sdiff_unique
  · (fail_if_success grind); (fail_if_success simp only [*, bool_simp]); sorry
  · (fail_if_success grind); (fail_if_success simp only [*, bool_simp]); sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sup

example : x \ y = x ↔ Disjoint y x := by
  fail_if_success grind [sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, disjoint_iff]
  fail_if_success simp only [*, bool_simp, sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, disjoint_iff]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_eq_self_iff_disjoint

example (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  fail_if_success grind [inf_eq_right]
  fail_if_success simp only [*, bool_simp, inf_eq_right]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_lt

example : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  fail_if_success grind
  fail_if_success simp only [*, bool_simp]
  sorry

/- Previous -/ attribute [grind, bool_simp] sup_inf_inf_sdiff

example : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · (fail_if_success grind); (fail_if_success simp only [*, bool_simp]); sorry
  · (fail_if_success grind); (fail_if_success simp only [*, bool_simp]); sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sdiff_right

example : x \ (y \ z) = x \ y ⊔ x ⊓ z := by
  grind

example : x \ (y \ z) = x \ y ⊔ x ⊓ z := by
  fail_if_success simp only [*, bool_simp]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sdiff_right'

example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  calc
  z \ (x \ y ⊔ y \ x)
  _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by grind
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x)     := by (fail_if_success grind); sorry
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x))       := by (fail_if_success grind); sorry
  _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)         := by grind
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)             := by grind

example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  calc
  z \ (x \ y ⊔ y \ x)
  _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x) := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x)     := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x))       := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)         := by (fail_if_success simp only [*, bool_simp]); sorry
  _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)             := by (fail_if_success simp only [*, bool_simp]); sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sdiff_sup_sdiff

example : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by
  grind

example : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by
  fail_if_success simp only [*, bool_simp]
  sorry

/- Previous -/ attribute [grind, bool_simp] sdiff_sdiff_sup_sdiff'

example : (x ⊓ y) \ z = x \ z ⊓ y \ z := by
  apply sdiff_unique <;> fail_if_success grind <;> fail_if_success simp only [*, bool_simp]
  all_goals sorry

/- Previous -/ attribute [grind, bool_simp] inf_sdiff

example (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z := by
  apply sdiff_unique
  · (fail_if_success grind [inf_bot_eq]); sorry
  · grind [inf_bot_eq]

  example (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z := by
  apply sdiff_unique
  · (fail_if_success simp only [*, bool_simp, inf_bot_eq]); sorry
  · (fail_if_success simp only [*, bool_simp, inf_bot_eq]); sorry

/- Previous -/ attribute [grind, bool_simp] inf_sdiff_assoc

example : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y := by
  fail_if_success grind
  fail_if_success simp only [*, bool_simp]
  sorry

/- Previous -/ attribute [grind, bool_simp] sup_eq_sdiff_sup_sdiff_sup_inf
