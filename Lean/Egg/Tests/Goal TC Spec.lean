import Egg

class CommAdd (α) extends Add α where
  comm : ∀ a b : α, a + b = b + a

instance : CommAdd Nat where
  comm := Nat.add_comm

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.genGoalTcSpec false in
example (a : Nat) : a + b = b + a := by
  egg [CommAdd.comm]

set_option egg.genGoalTcSpec true in
example (a : Nat) : a + b = b + a := by
  egg [CommAdd.comm]
