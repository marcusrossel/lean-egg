import Egg

-- This used to get stuck before eqsat because of a bug causing non-termination in the loop
-- generating derived rewrites.

variable
  {n : Nat} {p : Nat → Prop} [inst : DecidablePred p]
  {find : [DecidablePred p] → (∃ n, p n) → Nat}
  {find_lt_iff : ∀ (h : ∃ y : Nat, p y) (n : Nat), find h < n ↔ ∃ m < n, p m}

include find_lt_iff in
theorem find_le_iff (h : ∃ z : Nat, p z) (n : Nat) : find h ≤ n ↔ ∃ m ≤ n, p m := by
  egg [exists_prop, Nat.lt_succ_iff, find_lt_iff]
