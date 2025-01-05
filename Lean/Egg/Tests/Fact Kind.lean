import Egg

/--
error: egg requires premises to be (proofs of) propositions or (non-propositional) definitions
-/
#guard_msgs in
example (h : Nat) : 0 = 0 := by
  egg [h]

set_option linter.unusedVariables false in
example (h : True ∧ False) : 0 = 0 := by
  egg [h]

/--
error: egg requires premises to be (proofs of) propositions or (non-propositional) definitions
-/
#guard_msgs in
example (h : Inhabited Nat) : 0 = 0 := by
  egg [h]
