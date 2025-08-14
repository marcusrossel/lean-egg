import Egg

-- These tests check that automatic introduction of antecedents is compatible with conditional
-- rewriting, in the sense that conditional rewrites can use the introduced hypotheses, and proof
-- reconstruction works as expected.

example {P₁ P₂ : Prop} (h : P₁ → P₂) : P₁ → P₂ := by
  egg [h]

example {P : Prop} (h : 0 = 1 → P) : 0 = 1 → P := by
  egg [h]

example {x y : Nat} {P : Prop} (h : x = y → P) : x = y → P := by
  egg [h]

example (h : ∀ x y : Nat, x = y → y + y = x) {a b : Nat} : a = b → b + b = a := by
  egg [h]
