import Egg

-- This tests that we correctly encode bound variables appearing in binder domains. This previously
-- failed with `unexpected bound variable #0`.

variable (h : True ↔ ∀ (a : Nat) (_ : a > 0), True)

example : True ↔ ∀ (a : Nat) (_ : a > 0), True := by
  egg [h]
