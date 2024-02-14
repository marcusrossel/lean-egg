import Egg

-- Tests for different variants of declaring and using hypotheses.

example (a b : Nat) : a + b = b + a := by
  have h := Nat.add_comm
  egg [h]

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a :=
  fun h => by egg [h]

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a :=
  (by egg [·])

example (a : Nat) : a + 1 = 1 + a := by
  egg [(fun _ => Nat.add_comm .. : ∀ x, x + 1 = 1 + x)]

example (a : Nat) : (∀ x, x + 1 = 1 + x) → a + 1 = 1 + a :=
  fun _ => by egg [‹∀ _ : Nat, _›]

variable (h : ∀ x, x + 1 = 1 + x) in
example (a : Nat) : a + 1 = 1 + a := by
  egg [h]

variable {h : ∀ x, x + 1 = 1 + x} in
example (a : Nat) : a + 1 = 1 + a := by
  egg [h]
