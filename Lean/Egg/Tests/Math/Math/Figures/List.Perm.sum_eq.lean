import Mathlib
import Egg

set_option pp.explicit true
set_option trace.egg true

example {M} [AddCommMonoid M] {l₁ l₂ : List M} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  egg [List.Perm.sum_eq, *]
