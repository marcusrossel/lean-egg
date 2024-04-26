import Egg

example (x : Nat) (h₁ : ∀ n, n > 2 → n = x) (h₂ : 3 > 2) : 3 = x := by
  egg (config := { exitPoint := some .beforeProof }) [h₁, h₂]
