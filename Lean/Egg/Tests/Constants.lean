import Egg

axiom ax : 1 = 2

example : 1 = 2 := by
  egg [ax]

/--
error: egg requires arguments to be (proofs of) propositions or (non-propositional) definitions
-/
#guard_msgs in
example : 0 = 0 := by
  egg [Nat]

opaque op : Nat

/--
error: egg requires arguments to be (proofs of) propositions or (non-propositional) definitions
-/
#guard_msgs in
example : 0 = 0 := by
  egg [op]

opaque thm : 0 = 0 := rfl

example : 0 = 0 := by
  egg [thm]
