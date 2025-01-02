import Egg

/-- error: egg requires facts to be proofs or type class instances -/
#guard_msgs in
example (h : Nat) : 0 = 0 := by
  egg [; h]

set_option linter.unusedVariables false

example (h : True ∧ False) : 0 = 0 := by
  egg [; h]

example (h : Inhabited Nat) : 0 = 0 := by
  egg [; h]
