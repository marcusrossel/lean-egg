import Egg

-- Tests for the equations generated for non-recursive functions.

def f : Bool → Nat
  | false => 0
  | true => 1

example : f false = 0 := by
  egg [f]
