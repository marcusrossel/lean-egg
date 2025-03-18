import Egg
import Mathlib

attribute [egg neg] not_not
attribute [egg neg] Classical.not_imp -- TODO: Why doesn't `_root_.not_imp` work?
attribute [egg neg] not_iff
attribute [egg neg] not_or
attribute [egg neg] not_and
attribute [egg neg] not_and_or
attribute [egg neg] not_forall
attribute [egg neg] not_exists

-- TODO: Changing this `=` to a `↔` exposes the problem of instantiating erased equivalences with
--       `Eq`, instead of distinguishing between `Eq` and `Iff`.
--       Andrés Idea: During proof reconstruction, if defeq with `Eq` fails, try replacing it with
--       `Iff`.
example : ¬¬(p = p) := by
  egg neg

example : (¬¬p) ↔ p := by
  egg neg

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  egg neg

-- TODO: This will work again once `imp_mp` is reintroduced as an egg builtin.
example : ¬(p ∧ q) → (p → ¬q) := by
  egg neg

example (r : α → Prop) : (∀ x, ¬ r x) → ¬(∃ x, r x) := by
  egg neg
