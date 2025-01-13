import Egg
import Mathlib

attribute [egg] not_not
attribute [egg] Classical.not_imp -- TODO: Why doesn't `_root_.not_imp` work?
attribute [egg] not_iff
attribute [egg] not_or
attribute [egg] not_and
attribute [egg] not_and_or
attribute [egg] not_forall
attribute [egg] not_exists

-- TODO: Changing this `=` to a `↔` exposes the problem of instantiating erased equivalences with
--       `Eq`, instead of distinguishing between `Eq` and `Iff`.
example : ¬¬(p = p) := by
  egg!

example : (¬¬p) ↔ p := by
  egg!

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  egg!

example : ¬(p ∧ q) → (p → ¬q) := by
  egg!

example (r : α → Prop) : (∀ x, ¬ r x) → ¬(∃ x, r x) := by
  egg!
