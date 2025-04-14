import Egg
import Mathlib.Order.BooleanAlgebra

attribute [egg ac] sup_comm sup_assoc inf_comm inf_assoc

variable [GeneralizedBooleanAlgebra α] {x y z : α}

-- sdiff_unique
set_option trace.egg true in
example (s : x ⊓ y ⊔ z = x) (i : x ⊓ y ⊓ z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  -- TODO: eq_of_inf_eq_sup_eq is another example where we need the unbound vars for proof reconstr.
  egg [eq_of_inf_eq_sup_eq, i, s]
  -- exact (eq_of_inf_eq_sup_eq i s).symm

theorem sdiff_le' : x \ y ≤ x := by
  egg [le_sup_right, sup_inf_sdiff] using x ⊓ y ⊔ x \ y

-- TODO: What do we need to replicate ac_rfl?

theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x := by
  egg ac [sup_inf_self, sup_inf_sdiff] using y \ x ⊔ (x ⊔ x ⊓ y)

#check sdiff_inf_sdiff
example : x \ y ⊓ y \ x = ⊥ := by
  egg ac [inf_inf_sdiff, sup_inf_sdiff, inf_sup_left, inf_idem, inf_sup_right, bot_sup_eq,
          inf_of_le_right (α := α) sdiff_le']
    using x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y

#check inf_sdiff_self_right
example : x ⊓ y \ x = ⊥ := by
  egg [sup_inf_sdiff, inf_sup_right, inf_comm, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
    using (x ⊓ y ⊔ x \ y)

#check sdiff_sup
example : y \ (x ⊔ z) = y \ x ⊓ y \ z := by
  apply sdiff_unique
  · egg ac [sup_inf_left, inf_sup_left, sup_inf_sdiff, sup_inf_sdiff, sup_inf_self, inf_idem]
      using (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z))
  · egg ac [inf_sup_left, inf_sup_right, inf_inf_sdiff, bot_inf_eq, bot_sup_eq, inf_inf_sdiff, inf_bot_eq]
      using (y ⊓ x ⊔ y ⊓ z) ⊓ (y \ x ⊓ y \ z)

-- sdiff_eq_self_iff_disjoint
example : x \ y = x ↔ Disjoint y x := by
  egg [sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, inf_bot_eq, inf_comm, disjoint_iff]

-- sdiff_lt
example (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  egg [sdiff_eq_self_iff_disjoint', disjoint_iff, h, inf_eq_right.mpr hx]

-- sup_inf_inf_sdiff
example : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  egg [inf_assoc, sup_inf_right, sup_inf_sdiff, inf_sup_right, inf_sdiff_left]

#check sdiff_sdiff_right
example : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · egg ac calc [sup_inf_right, sup_inf_self, sup_sdiff_left, sup_inf_left, sdiff_sup_self',
                 inf_sup_right, sup_inf_sdiff, inf_sdiff_sup_right, inf_sup_left, inf_sup_self]
      _ = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y))
      _ = x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y)
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y)))
      _ = _
  · egg ac [inf_sup_left, inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq, inf_sdiff_left,
            inf_sdiff_self_right]
      using x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y

#check sdiff_sdiff_right'
example : x \ (y \ z) = x \ y ⊔ x ⊓ z := by
  egg ac [sdiff_sdiff_right, sup_inf_inf_sdiff]

#check sdiff_sdiff_sup_sdiff
example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  egg ac [sdiff_sup, sdiff_sdiff_right, sup_inf_left, sup_inf_sdiff, inf_idem]
    using z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)

#check sdiff_sdiff_sup_sdiff'
example : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by
  egg ac [sdiff_sup, sdiff_sdiff_right, sup_inf_right]

#check inf_sdiff
example : (x ⊓ y) \ z = x \ z ⊓ y \ z := by
  apply sdiff_unique
  all_goals egg ac [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq, sup_inf_left, sup_inf_right,
                    sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right, inf_sup_self,
                    sup_inf_inf_sdiff, sup_eq_left, (inf_le_inf (α := α) sdiff_le sdiff_le)]

#check inf_sdiff_assoc
example (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z := by
  apply sdiff_unique <;> egg ac [inf_assoc, inf_sup_left, sup_inf_sdiff, inf_inf_sdiff, inf_bot_eq]

#check sup_eq_sdiff_sup_sdiff_sup_inf
example : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y := by
  egg ac [sup_inf_left, sup_sdiff_right, sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]

-- TODO: Check out some of the theorems in BooleanAlgebra.lean
#check BooleanAlgebra
