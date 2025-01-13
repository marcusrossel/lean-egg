import Egg
open scoped Egg

set_option egg.derivedGuides true
set_option egg.builtins false
set_option egg.genTcProjRws false

-- TODO: Add tracing for guides and guard messages:

example (h : 0 = 0) : 0 = 0 := by
  egg [h]

example (h : ∀ x : Nat, x = 0) : 0 = 0 := by
  egg [h]

example (h : ∀ p q : Prop, p ∧ q) : 0 = 0 := by
  egg [h]

example (h : ∀ p q : Prop, (1 = 2) → p ∧ q) : 0 = 0 := by
  egg [h]

example (h : (∀ p : Prop, p) ↔ (∀ q : Prop, q)) : 0 = 0 := by
  egg [h]

example (h : ∀ a : Prop, (∀ p : Prop, a ∧ p) ↔ (∀ q : Prop, q)) : 0 = 0 := by
  egg [h]
