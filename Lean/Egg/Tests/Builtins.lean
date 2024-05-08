import Egg

/-- error: egg failed to prove goal -/
#guard_msgs in
set_option egg.builtins false in
example : Nat.succ a = a + 1 := by
  egg

set_option egg.builtins true in
example : Nat.succ a = a + 1 := by
  egg
