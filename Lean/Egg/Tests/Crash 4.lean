import Egg

-- This used to fail because we were not considering proof mvars when refreshing a rewrite's mvars.
-- As a result, rewrites produced by type class specialization could contain unrefreshed mvars for
-- proof terms (and their types). These did not affect the computation of valid directions, but did
-- affect the encoding of erased proofs which then contained mvars which should have been assigned
-- by type class specialization. As a result, `union_instantiations` would crash with the
-- substitution lacking an assignment for the pattern variable corresponding to the non-refreshed
-- proof mvar.

variable
  {n : Nat} {p : Nat → Prop} [inst : DecidablePred p]
  {find : [DecidablePred p] → (∃ n, p n) → Nat}
  {find_lt_iff : ∀ (h : ∃ y : Nat, p y) (n : Nat), find h < n ↔ ∃ m < n, p m}

include find_lt_iff in
theorem find_le_iff (h : ∃ z : Nat, p z) (n : Nat) : find h ≤ n ↔ ∃ m ≤ n, p m := by
  egg [exists_prop, Nat.lt_succ_iff, find_lt_iff; inst]
