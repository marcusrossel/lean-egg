import Egg

-- Tests for the `egg [*]` construct.

example : True := by
  fail_if_success have : true = false := by egg [*]
  constructor

example (_ : 0 = 0) : 1 + 1 = 2 := by
  fail_if_success egg [*]
  rfl

example : 0 = 0 := by
  egg [*]

example (a : Nat) : a = a := by
  egg [*]

example (a b : Nat) (_ : a = b) : a = b := by
  egg [*]

example (a b c : Nat) (_ : a = b) (_ : b = c) : a = c := by
  egg [*]

example (a b : Nat) : a + b = b + a := by
  have := Nat.add_comm
  egg [*]

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  have := Nat.add_comm
  have := Nat.add_assoc
  egg [*]
