import Egg

class CommAdd (α) extends Add α where
  comm : ∀ a b : α, a + b = b + a

instance : CommAdd Nat where
  comm := Nat.add_comm

/-- error: egg failed to prove goal -/
#guard_msgs in
set_option egg.eagerTcSpec false in
example (a : Nat) : a + b = b + a := by
  letI := inferInstanceAs <| CommAdd Nat
  egg [CommAdd.comm]

set_option egg.eagerTcSpec true in
example (a : Nat) : a + b = b + a := by
  letI := inferInstanceAs <| CommAdd Nat
  egg [CommAdd.comm]
