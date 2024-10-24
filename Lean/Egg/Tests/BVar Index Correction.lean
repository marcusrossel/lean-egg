import Egg

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

-- We have to disable β-reduction as part of normalization, as otherwise `thm₁,₂` are useless, and
-- disable β-reduction in egg, as this interferes with the test cases.
set_option egg.betaReduceRws false
set_option egg.genBetaRw false

-- This theorem is only applicable in the forward direction.
theorem thm₁ : ∀ x y : Nat, (x, y).fst = (fun _ => x) (nat_lit 1) :=
  fun _ _ => rfl

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example : (fun x => (x, 5).fst) = (fun _ : Nat => (fun x => x) 1) := by
  egg [thm₁]
