import Egg

-- Tests for the `*` argument.

/-- error: egg failed to prove goal -/
#guard_msgs in
example : true = false := by
  egg [*]

/-- error: egg failed to prove goal -/
#guard_msgs in
example (_ : true = true) : [true] ++ [] = [true] := by
  egg [*]

/-- error: duplicate '*' in arguments to egg -/
#guard_msgs in
example : 0 = 0 := by
  egg [*, *]

/-- error: duplicate '*' in arguments to egg -/
#guard_msgs in
example (h : 0 = 0) : 0 = 0 := by
  egg [*, h, *]

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

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  have := Nat.add_assoc
  egg [*, Nat.add_comm]

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  have := Nat.add_assoc
  egg [Nat.add_comm, *]

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  egg [Nat.add_comm, *, Nat.add_assoc]
