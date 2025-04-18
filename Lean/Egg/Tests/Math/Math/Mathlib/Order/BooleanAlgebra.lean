import Egg
import Mathlib.Order.BooleanAlgebra

-- TODO: It would be convenient to have a command for extending a given egg basket.
-- TODO: I think having the better heuristic for generated rewrites is really important here.

set_option egg.timeLimit 5
set_option egg.genTcProjRws false -- TODO: Things still work if we keep this, but it seems not to be necessary.
set_option egg.genGoalTcSpec true -- TODO: This is actually necessary.
set_option egg.genGroundEqs false -- TODO: Things still work if we keep this, but it seems not to be necessary.

-- SemilatticeSup
attribute [egg slattice] /- le_sup_left le_sup_right le_sup_of_le_left le_sup_of_le_right
                         lt_sup_of_lt_left lt_sup_of_lt_right sup_le sup_le_iff sup_eq_left
                         sup_eq_right left_eq_sup right_eq_sup left_lt_sup right_lt_sup
                         left_or_right_lt_sup le_iff_exists_sup sup_le_sup sup_le_sup_left
                         sup_le_sup_right -/ sup_idem sup_comm sup_assoc sup_left_right_swap
                         sup_left_idem sup_right_idem sup_left_comm sup_right_comm sup_sup_sup_comm
                         sup_sup_distrib_left sup_sup_distrib_right sup_congr_left sup_congr_right
                         /- sup_eq_sup_iff_left sup_eq_sup_iff_right Ne.lt_sup_or_lt_sup -/

-- SemilatticeInf
attribute [egg ilattice] /- inf_le_left inf_le_right le_inf inf_le_of_left_le inf_le_of_right_le
                         inf_lt_of_left_lt inf_lt_of_right_lt le_inf_iff inf_eq_left le_of_inf_eq -/
                         inf_of_le_left /- inf_eq_right -/ inf_of_le_right /- left_eq_inf
                         right_eq_inf inf_lt_left inf_lt_right inf_lt_left_or_right
                         inf_le_inf inf_le_inf_right inf_le_inf_left -/ inf_idem inf_comm inf_assoc
                         inf_left_right_swap inf_left_idem inf_right_idem inf_left_comm
                         inf_right_comm inf_inf_inf_comm inf_inf_distrib_left inf_inf_distrib_right
                         inf_congr_left inf_congr_right /- inf_eq_inf_iff_left inf_eq_inf_iff_right
                         Ne.inf_lt_or_inf_lt -/

-- Lattice
attribute [egg lattice] /- inf_le_sup sup_le_inf inf_eq_sup sup_eq_inf inf_lt_sup
                        inf_eq_and_sup_eq_iff sup_inf_le le_inf_sup -/ inf_sup_self sup_inf_self
                        /- sup_eq_iff_inf_eq -/

-- DistribLattice
attribute [egg dlattice] /- le_sup_inf -/ sup_inf_left sup_inf_right inf_sup_left inf_sup_right
                         /- le_of_inf_le_sup_le -/ eq_of_inf_eq_sup_eq

-- Axioms of GeneralizedBooleanAlgebra
attribute [egg gbool] sup_inf_sdiff inf_inf_sdiff

-- Combines slattice ilattice lattice dlattice and gbool
attribute [egg bool] True.intro

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
  egg ac gbool [le_sup_right] using x ⊓ y ⊔ x \ y

theorem sdiff_sup_self' : y \ x ⊔ x = y ⊔ x := by
  egg ac gbool lattice ilattice using y \ x ⊔ (x ⊔ x ⊓ y)

#check sdiff_inf_sdiff
example : x \ y ⊓ y \ x = ⊥ := by
  sorry -- TODO: This started breaking when we started generating fewer goal tc spec rewrites and
        --       turned off some of the other gen options.
    -- egg [inf_comm, inf_assoc, inf_inf_sdiff, inf_sup_left, inf_idem, inf_sup_right, bot_sup_eq, inf_of_le_right (α := α) sdiff_le']
    --   using x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y

#check sdiff_inf_sdiff
example : x \ y ⊓ y \ x = ⊥ :=
  Eq.symm <| by
    egg slattice ilattice lattice dlattice gbool calc [bot_sup_eq, inf_of_le_right (α := α) sdiff_le']
      _ = x ⊓ y ⊓ x \ y
      _ = x ⊓ (y ⊓ x ⊔ y \ x) ⊓ x \ y
      _ = (x ⊓ (y ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y
      _ = (y ⊓ (x ⊓ x) ⊔ x ⊓ y \ x) ⊓ x \ y
      _ = (y ⊓ x ⊔ x ⊓ y \ x) ⊓ x \ y
      _ = x ⊓ y ⊓ x \ y ⊔ x ⊓ y \ x ⊓ x \ y
      _ = x ⊓ y \ x ⊓ x \ y
      _ = x ⊓ x \ y ⊓ y \ x
      _ = x \ y ⊓ y \ x

#check inf_sdiff_self_right
example : x ⊓ y \ x = ⊥ := by
  egg ac gbool [inf_sup_right, sdiff_inf_sdiff, bot_sup_eq] using (x ⊓ y ⊔ x \ y)

#check inf_sdiff_self_right
example : x ⊓ y \ x = ⊥ := by
  egg slattice ilattice lattice dlattice gbool calc [sdiff_inf_sdiff, bot_sup_eq]
    x ⊓ y \ x = (x ⊓ y ⊔ x \ y) ⊓ y \ x
    _ = x ⊓ y ⊓ y \ x ⊔ x \ y ⊓ y \ x
    _ = _

#check sdiff_sup
example : y \ (x ⊔ z) = y \ x ⊓ y \ z := by
  apply sdiff_unique
  · egg ac gbool [sup_inf_left, inf_sup_left, sup_inf_self, inf_idem]
      using (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z))
  · egg ac gbool [inf_sup_left, inf_sup_right, bot_inf_eq, bot_sup_eq, inf_bot_eq]
      using (y ⊓ x ⊔ y ⊓ z) ⊓ (y \ x ⊓ y \ z)

#check sdiff_eq_self_iff_disjoint
example : x \ y = x ↔ Disjoint y x := by
  egg ac gbool [sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, inf_bot_eq, disjoint_iff]

#check sdiff_eq_self_iff_disjoint
example : x \ y = x ↔ Disjoint y x := by
  egg slattice ilattice lattice dlattice gbool calc [sdiff_bot, sdiff_eq_sdiff_iff_inf_eq_inf, inf_bot_eq, disjoint_iff]
    x \ y = x ↔ x \ y = x \ ⊥
    _ ↔ x ⊓ y = x ⊓ ⊥
    _ ↔ Disjoint y x

#check sdiff_lt
example (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine sdiff_le.lt_of_ne fun h => hy ?_
  egg slattice ilattice lattice dlattice gbool [sdiff_eq_self_iff_disjoint', disjoint_iff, h, inf_eq_right.mpr hx]

#check sup_inf_inf_sdiff
example : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  egg ac gbool [sup_inf_right, inf_sup_right, inf_sdiff_left]

#check sup_inf_inf_sdiff
set_option trace.egg true in
example : x ⊓ y ⊓ z ⊔ y \ z = x ⊓ y ⊔ y \ z := by
  egg slattice ilattice lattice dlattice gbool calc [inf_sdiff_left]
    x ⊓ y ⊓ z ⊔ y \ z = x ⊓ (y ⊓ z) ⊔ y \ z
    _ = (x ⊔ y \ z) ⊓ y
    _ = x ⊓ y ⊔ y \ z

#check sdiff_sdiff_right
example : x \ (y \ z) = x \ y ⊔ x ⊓ y ⊓ z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · egg ac gbool calc [sup_inf_right, sup_inf_self, sup_sdiff_left, sup_inf_left, sdiff_sup_self',
                 inf_sup_right, inf_sdiff_sup_right, inf_sup_left, inf_sup_self]
      _ = (x ⊔ (z ⊓ x ⊔ x \ y)) ⊓ (y \ z ⊔ (z ⊓ x ⊔ x \ y))
      _ = x ⊓ (y \ z ⊓ (z ⊔ y) ⊔ x ⊓ (z ⊔ y) ⊔ x \ y)
      _ = x ⊓ (y \ z ⊔ (x ⊓ z ⊔ (x ⊓ y ⊔ x \ y)))
      _ = _
  · egg ac gbool [inf_sup_left, inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq, inf_sdiff_left,
            inf_sdiff_self_right]
      using x ⊓ y \ z ⊓ (z ⊓ x) ⊔ x ⊓ y \ z ⊓ x \ y

#check sdiff_sdiff_right'
example : x \ (y \ z) = x \ y ⊔ x ⊓ z := by
  egg ac gbool [sdiff_sdiff_right, sup_inf_inf_sdiff]

#check sdiff_sdiff_sup_sdiff
example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  egg ac gbool [sdiff_sup, sdiff_sdiff_right, sup_inf_left, inf_idem]
    using z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)

#check sdiff_sdiff_sup_sdiff'
example : z \ (x \ y ⊔ y \ x) = z ⊓ x ⊓ y ⊔ z \ x ⊓ z \ y := by
  egg ac gbool [sdiff_sup, sdiff_sdiff_right, sup_inf_right]

#check inf_sdiff
example : (x ⊓ y) \ z = x \ z ⊓ y \ z := by
  apply sdiff_unique
  all_goals egg ac gbool [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq, sup_inf_left, sup_inf_right,
                    sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right, inf_sup_self,
                    sup_inf_inf_sdiff, sup_eq_left, (inf_le_inf (α := α) sdiff_le sdiff_le)]

#check inf_sdiff_assoc
example (x y z : α) : (x ⊓ y) \ z = x ⊓ y \ z := by
  apply sdiff_unique <;> egg ac gbool [inf_sup_left, inf_bot_eq]

#check sup_eq_sdiff_sup_sdiff_sup_inf
example : x ⊔ y = x \ y ⊔ y \ x ⊔ x ⊓ y := by
  egg ac gbool [sup_inf_left, sup_sdiff_right, sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]
