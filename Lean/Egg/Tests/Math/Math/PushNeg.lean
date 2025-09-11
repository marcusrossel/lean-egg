import Egg
import Mathlib

attribute [egg neg] Ne not_not _root_.not_imp not_iff not_or not_and not_and_or not_forall not_exists

-- NOTE: The following example relies on backtracking for choosing between `=` and `↔` when
--       constructing proofs of reified equivalences.
example : ¬¬(p ↔ p) := by
  egg +neg

example : ¬¬(p = p) := by
  egg +neg

example : ¬(p ≠ p) := by
  egg +neg

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  egg +neg

-- NOTE: This relies on the builtin theorem for modus ponens, and hence assignment of weak vars.
example : ¬(p ∧ q) → (p → ¬q) := by
  egg +neg

example (r : α → Prop) : (∀ x, ¬r x) → ¬(∃ x, r x) := by
  egg +neg
