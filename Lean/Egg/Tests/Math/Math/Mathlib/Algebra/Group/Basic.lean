import Math.Mathlib.Algebra.Group.Defs

-- NOTE: Starting around line 110.

section CommSemigroup

variable [CommSemigroup G]

example (a b c : G) : a * (b * c) = b * (a * c) := by
  egg +comm_semigroup

/- Previous -/ attribute [egg comm_semigroup] mul_left_comm

example (a b c : G) : a * b * c = a * c * b := by
  egg +comm_semigroup

/- Previous -/ attribute [egg comm_semigroup] mul_right_comm

example (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  egg +comm_semigroup

/- Previous -/ attribute [egg comm_semigroup] mul_mul_mul_comm

example (a b c : G) : a * b * c = b * c * a := by
  egg +comm_semigroup

/- Previous -/ attribute [egg comm_semigroup] mul_rotate

example (a b c : G) : a * (b * c) = b * (c * a) := by
  egg +comm_semigroup

/- Previous -/ attribute [egg comm_semigroup] mul_rotate'

end CommSemigroup

-- NOTE: Skipped monoid power theorems around lines 130-200.

section CommMonoid

example (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  sorry -- TODO: This used to work: egg +comm_monoid [*]

/- Previous -/ attribute [egg comm_monoid] inv_unique

end CommMonoid

-- NOTE: Skipped lines 210+.
