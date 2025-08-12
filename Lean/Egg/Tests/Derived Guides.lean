import Egg

set_option egg.derivedGuides true
set_option egg.builtins false
set_option egg.tcProjs false

set_option trace.egg.guides true
set_option linter.unusedVariables false

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: 0
  [egg.guides] ↣1!: 0 = 0
-/
#guard_msgs in
example (h : 0 = 0) : 0 = 0 := by
  egg [h]

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: ∀ (x : Nat), x = 0
  [egg.guides] ↣1!: True
  [egg.guides] ↣2!: 0
  [egg.guides] ↣3!: 0 = 0
-/
#guard_msgs in
example (h : ∀ x : Nat, x = 0) : 0 = 0 := by
  egg [h]

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: ∀ (p q : Prop), p ∧ q
  [egg.guides] ↣1!: True
  [egg.guides] ↣2!: And
  [egg.guides] ↣3!: 0 = 0
-/
#guard_msgs in
example (h : ∀ p q : Prop, p ∧ q) : 0 = 0 := by
  egg [h]

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: ∀ (p q : Prop), 1 = 2 → p ∧ q
  [egg.guides] ↣1!: True
  [egg.guides] ↣2!: And
  [egg.guides] ↣3!: 1 = 2
  [egg.guides] ↣4!: 0 = 0
-/
#guard_msgs in
example (h : ∀ p q : Prop, (1 = 2) → p ∧ q) : 0 = 0 := by
  egg [h]

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: ∀ (q : Prop), q
  [egg.guides] ↣1!: 0 = 0
-/
#guard_msgs in
example (h : (∀ p : Prop, p) ↔ (∀ q : Prop, q)) : 0 = 0 := by
  egg [h]

/--
trace: [egg.guides] Guides
  [egg.guides] ↣0!: ∀ (a : Prop), (∀ (p : Prop), a ∧ p) ↔ ∀ (q : Prop), q
  [egg.guides] ↣1!: ∀ (q : Prop), q
  [egg.guides] ↣2!: Prop
  [egg.guides] ↣3!: True
  [egg.guides] ↣4!: And
  [egg.guides] ↣5!: 0 = 0
-/
#guard_msgs in
example (h : ∀ a : Prop, (∀ p : Prop, a ∧ p) ↔ (∀ q : Prop, q)) : 0 = 0 := by
  egg [h]
