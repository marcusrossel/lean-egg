import Egg

example : True := by
  fail_if_success have : true = false := by egg
  constructor

example : True := by
  fail_if_success have : True := by egg
  constructor

example : True := by
  fail_if_success have : true = true := by egg [true]
  constructor

set_option trace.egg true in
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
  | .zero => .zero
  | n + 1 => f n

def g : Nat → Nat
  | .zero => .zero
  | n + 1 => g n

example : f (g Nat.zero.succ.succ) = .zero := by
  egg [f, g]
