import Egg
import Lean

set_option egg.eraseTCInstances true
set_option egg.genTcSpecRws false
set_option trace.egg true

theorem t [Inhabited Nat] (a b : Nat) : Nat.add a b = Nat.add b a := sorry

-- TODO: This doesn't work yet.
example [Inhabited Nat] (a b : Nat) : Nat.add a b = Nat.add b a := by
  sorry -- egg [t]
