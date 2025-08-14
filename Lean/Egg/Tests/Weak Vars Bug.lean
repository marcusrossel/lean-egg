import Egg

example {P : Prop} (h : ∀ x y : Nat, x = y → P) {a b : Nat} : a = b → P := by
  sorry -- egg [h]
