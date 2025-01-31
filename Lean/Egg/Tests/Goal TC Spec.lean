import Egg

-- TODO: The example used to fail if we turned off goal-type spec *and* type class instance erasure.
--       Now that type class instance erasure is fixed, do we still need this test case?

set_option egg.genTcSpecRws true

class CommAdd (α) extends Add α where
  comm : ∀ a b : α, a + b = b + a

instance : CommAdd Nat where
  comm := Nat.add_comm

set_option egg.genGoalTcSpec true in
example (a : Nat) : a + b = b + a := by
  egg [CommAdd.comm]
