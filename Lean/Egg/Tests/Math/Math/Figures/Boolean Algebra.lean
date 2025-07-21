import Egg
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic

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

example : y \ x ⊔ x = y ⊔ x := by
  egg +bool calc
    y \ x ⊔ x
    _ = y \ x ⊔ (x ⊔ x ⊓ y)
    _ = y ⊓ x ⊔ y \ x ⊔ x
    _ = y ⊔ x

-- Note: These lemmas originate from `Mathlib.Order.BooleanAlgebra.Defs` and proceed the proof of
--       the following theorem. We can prove these lemmas (and others) lemmas using `egg +bool`. We
--       just omit those proofs here for brevity.
attribute [egg bool] inf_sdiff_right sdiff_sup sdiff_sdiff_right sdiff_sdiff_right'

example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  egg +bool calc
    z \ (x \ y ⊔ y \ x)
    _ = (z \ x ⊔ z ⊓ x ⊓ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x)
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ z ⊓ y ⊓ x)
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z ⊓ (z \ y ⊔ x))
    _ = z ⊓ z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)
    _ = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x)

example : z \ (x \ y ⊔ y \ x) = z ⊓ (z \ x ⊔ y) ⊓ (z \ y ⊔ x) := by
  egg +bool using z \ x ⊔ z ⊓ x ⊓ y
