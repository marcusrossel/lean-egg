import Egg

abbrev E (G) [Mul G] := ∀ x y z : G, x = (y * x) * ((x * z) * z)

theorem thm [Mul G] (e : E G) : ∀ a b c : G, (a * (b * c)) * (b * c) = a * (b * c) := sorry

example [Mul G] (e : E G) : ∀ x y : G, x = y := by
  intro x y
  have e₂ : ∀ a : G, a = (x * a) * ((a * y) * y) := sorry
  egg (config := { exitPoint := some .beforeProof }) [e₂, thm; e]
