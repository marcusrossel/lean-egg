import Egg

def f : Bool → Nat
  | false => 0
  | true => 1

-- BUG: Cf. Issue #17
example : f false = 0 := by
  egg [f]
