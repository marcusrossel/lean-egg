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

/--
error: egg failed to build proof step 2: unification failure for LHS of rewrite #0:

  HAdd.hAdd (x + 0)
vs
  ?m.2213 (?m.2216 + 0)
in
  f 1 (x + 0 + 0)
and
  f 1 (x + 0)

• Types: ⏎
  ?m.2213: Nat → Nat
  ?m.2216: Nat

• Read Only Or Synthetic Opaque MVars: []
-/
#guard_msgs in
set_option egg.retryWithShapes false in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  -- The explanation is broken because `?m.2213 : Nat → Nat` is being matched against
  -- `HAdd.hAdd : Nat → Nat → Nat`. That is, the types don't match.
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
