import Egg

variable (h : ∀ (p : Nat → Nat) (x : Nat), p x = p (x + 0))

set_option egg.genTcProjRws false in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  egg [h]

example (f : Nat → Nat → Nat) : (f (nat_lit 1)) x = (f 1) (x + 0) := by
  egg [h]

example (f : Nat → Nat → Nat) : (f 1) x = (f (nat_lit 1)) (x + 0) := by
  egg [h]

example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + (nat_lit 0)) := by
  egg [h]

-- Note: This used to fail with a broken explanation, because `?m.2213 : Nat → Nat` was matched
-- against `HAdd.hAdd : Nat → Nat → Nat`. That is, the types didn't match.
-- This suddenly started working as part of the `better-facts` PR.
set_option egg.retryWithShapes false in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  egg [h]

set_option egg.shapes true in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  egg [h]

/--
error: tactic 'rewrite' failed, pattern is a metavariable
  ?p ?x
from equation
  ?p ?x = ?p (?x + 0)
h : ∀ (p : Nat → Nat) (x : Nat), p x = p (x + 0)
x : Nat
f : Nat → Nat → Nat
⊢ f 1 x = f 1 (x + 0)
-/
#guard_msgs in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  rw [h]

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  simp [h]
