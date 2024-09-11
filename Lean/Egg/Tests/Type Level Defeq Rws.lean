import Egg

-- This test case ensures that we allow type-level defeq rewrite in erased proof terms.

variable
  {n : Nat} {p : Nat → Prop} [inst : DecidablePred p]
  {find : (∃ n, p n) → Nat}
  {find_lt_iff : ∀ (h : ∃ n, p n) n, find h < n ↔ ∃ m < n, p m}

set_option linter.unusedSectionVars false in
include find_lt_iff in
theorem find_le_iff (h : ∃ n : Nat, p n) (n : Nat) : find h ≤ n ↔ ∃ m ≤ n, p m := by
  egg [exists_prop, Nat.lt_succ_iff, find_lt_iff]
