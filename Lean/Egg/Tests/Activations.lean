import Egg

set_option trace.egg.activations true
set_option egg.builtins false

/--
trace: [egg.activations] Activations
  [egg.activations] nat-lit: false
      level: false
      lambda: false
      forall: false
-/
#guard_msgs in
example : True := by
  egg

/--
trace: [egg.activations] Activations
  [egg.activations] nat-lit: true
      level: false
      lambda: false
      forall: false
-/
#guard_msgs in
example : 0 = 0 := by
  egg

/--
trace: [egg.activations] Activations
  [egg.activations] nat-lit: false
      level: false
      lambda: true
      forall: false
-/
#guard_msgs in
example : (fun x : Bool => x) true = id true := by
  egg [id]

/--
trace: [egg.activations] Activations
  [egg.activations] nat-lit: false
      level: false
      lambda: false
      forall: true
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (h : ∀ x : Nat, x = x) : True := by
  egg [h]

/--
trace: [egg.activations] Activations
  [egg.activations] nat-lit: false
      level: true
      lambda: false
      forall: false
-/
#guard_msgs in
example (x : α × β) : id x = x := by
  egg [id]
