import Egg

-- BUG: fixed by `(config := { genTcProjRws := false })`
example : (fun x : Nat => 0) = (fun x => 0 + 0) := by
  egg [Nat.add_zero]

-- BUG: not fixed by `(config := { genTcProjRws := false })`
example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg [Nat.zero_add]

example : (fun x => x) = (fun x => x + 0) := by
  egg [Nat.add_zero]

example : (fun x => x) = (fun x => 0 + x) := by
  egg [Nat.zero_add]

example (f : (Nat → Nat) → Bool) : f (fun x => x) = f (fun x => x + 0) := by
  egg [Nat.add_zero]

-- BUG: broke after removing the binder type from ∀
example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]
