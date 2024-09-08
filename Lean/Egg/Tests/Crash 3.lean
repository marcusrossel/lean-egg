import Egg

-- This used to crash because we were not considering proof erasure when determining a rewrite's
-- mvars, which resulted in allowed directions for rewrites which should not have been valid. As a
-- result the calls to `union_instantiations` in the `LeanApplier` would crash, because the
-- substitution resulting from e-matching was incomplete.

/-- error: egg received invalid explanation: step contains type-level rewrite in proof -/
#guard_msgs in
set_option egg.eraseProofs true in
theorem Array.extract_extract {s1 e2 e1 s2 : Nat} {a : Array α} (h : s1 + e2 ≤ e1) :
    (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  apply ext
  · simp only [size_extract]
    omega
  · intro i h1 h2
    egg [get_extract, Nat.add_assoc]
