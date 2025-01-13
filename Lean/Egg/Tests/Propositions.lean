import Egg

example : True := by
  egg

example : True ↔ True := by
  egg

example (p q : Prop) (h : p ↔ q) : p ↔ q := by
  egg [h]

example (x : Nat) : (x.add (.succ .zero) = x) ↔ ((Nat.succ .zero).add x = x) := by
  have h (x y : Nat) : x.add y = y.add x := Nat.add_comm ..
  egg [h]

example (h : False) : False := by
  egg [h]

example {p q r : Prop} (h₁ : p ∧ q) (h₂ : p ∧ q → r) : r := by
  egg [h₁, h₂]

-- These test were previously used for the legacy `from` construct.
section From
set_option linter.unusedVariables false

example (h : True) : True := by
  egg [h]

example (h : 0 = 0) : 0 = 0 := by
  egg [h]

example (a b : Nat) (h : a = b) : a = b := by
  egg [Nat.add_comm, h]

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

example (h : p ∧ q ∧ r) : r ∧ r ∧ q ∧ p ∧ q ∧ r ∧ p := by
  egg [and_comm, and_assoc, and_self, h]

example (P : Nat → Prop) (hp : P Nat.zero.succ) (h : ∀ n, P n ↔ P n.succ) :
    P Nat.zero.succ.succ.succ.succ := by
  egg [h, hp]

end From
