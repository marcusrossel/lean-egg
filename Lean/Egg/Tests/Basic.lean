import Egg

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example : true = false := by
  egg

/--
error: expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', but found:

  True
-/
#guard_msgs in
example : True := by
  egg

/-- error: egg requires arguments to be theorems, definitions or axioms -/
#guard_msgs in
example : true = true := by
  egg [true]

example : 0 = 0 := by
  egg

example (a : Nat) : a = a := by
  egg

example (a b : Nat) (h : a = b) : a = b := by
  egg [h]

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

example (a b : Nat) : a + b = b + a := by
  egg [Nat.add_comm]

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  egg [Nat.add_comm, Nat.add_assoc]

example (a : Nat) (h : ∀ x : Nat, x + 1 = 1 + x) : a + 1 = 1 + a := by
  egg [h]

def f : Nat → Nat
  | .zero   => .zero
  | .succ n => f n

def g : Nat → Nat
  | .zero   => .zero
  | .succ n => g n

example : f (g Nat.zero.succ.succ) = .zero := by
  egg [f, g]
