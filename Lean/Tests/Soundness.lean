import Egg

-- Tests containing examples of (potential) soundness issues.

example : False := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  have : 1 + 2 = 0 := by egg (config := { typeTags := .none }) [h]
  contradiction

example : True := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  fail_if_success have : 1 + 2 = 0 := by egg (config := { typeTags := .indices }) [h]
  constructor
