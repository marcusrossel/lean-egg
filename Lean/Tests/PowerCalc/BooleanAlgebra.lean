import Mathlib.Order.BooleanAlgebra
import Egg

variable {α : Type _} {x y z : α}
variable [GeneralizedBooleanAlgebra α]

theorem sdiff_sup_egg : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
      (by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        egg [rw1, rw2, rw3, rw4, rw5])
      (by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        egg [rw1, rw2, rw3, rw4, rw5])

theorem sdiff_sup_egg1 :
  y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        egg [rw1, rw2, rw3, rw4, rw5]

theorem sdiff_sup_egg2 :
  (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        egg [rw1, rw2, rw3, rw4, rw5]

theorem sdiff_sup_egg3 :
  (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        egg [rw1, rw2, rw3, rw4, rw5]
