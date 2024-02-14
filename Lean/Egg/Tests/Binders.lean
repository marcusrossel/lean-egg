import Egg

example : (fun x : Nat => 0) = (fun x => 0 + 0) := by
  egg [Nat.add_zero]

example : (fun x => x) = (fun x => x + 0) := by
  egg [Nat.add_zero]

example (f : (Nat → Nat) → Bool) : f (fun x => x) = f (fun x => x + 0) := by
  egg [Nat.add_zero]

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]
