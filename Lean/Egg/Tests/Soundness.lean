import Egg

-- Tests containing examples of backend soundness issues.

-- Note: The `sorry` indicates that egg found a proof, but we're not performing proof reconstruction
--       (which would be impossible) as a result of setting `exitPoint := .beforeProof`.
example : False := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  have : 1 + 2 = 0 := by egg (config := { exitPoint := .beforeProof }) [h]
  contradiction
