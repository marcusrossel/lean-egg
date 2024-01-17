import Egg

-- Tests containing examples of (potential) soundness issues.

-- Note: The `sorry` indicates that egg found a proof, but we're not performing proof reconstruction
--       (as this is impossible) as a result of setting `buildProof := false`.
example : False := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  have : 1 + 2 = 0 := by egg (config := { typeTags := .none, buildProof := false }) [h]
  contradiction

example : True := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  fail_if_success have : 1 + 2 = 0 := by egg (config := { typeTags := .indices }) [h]
  constructor
