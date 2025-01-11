import Egg

class CommAdd (α) extends Add α where
  comm : ∀ a b : α, a + b = b + a

instance : CommAdd Nat where
  comm := Nat.add_comm

set_option egg.genGoalTcSpec false in
example (a : Nat) : a + b = b + a := by
  -- TODO: What is the role of type class specialization now that we have type class instance
  --       erasure?
  fail_if_success egg [CommAdd.comm]

set_option egg.genGoalTcSpec true in
example (a : Nat) : a + b = b + a := by
  egg [CommAdd.comm]
