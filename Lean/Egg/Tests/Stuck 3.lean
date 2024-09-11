import Egg

-- This used to get stuck before eqsat because `Premises.gen.genTcRws` would only reassign
-- `projTodo` when `genTcSpecRws` was active, so setting that option to false would lead to an
-- infinite loop.

variable
  {n : Nat} {p : Nat → Prop} [inst : DecidablePred p]
  {find : [DecidablePred p] → (∃ n, p n) → Nat}
  {find_lt_iff : ∀ (h : ∃ y : Nat, p y) (n : Nat), find h < n ↔ ∃ m < n, p m}

set_option egg.genTcSpecRws false
include find_lt_iff in
theorem find_le_iff (h : ∃ z : Nat, p z) (n : Nat) : find h ≤ n ↔ ∃ m ≤ n, p m := by
  egg [exists_prop, Nat.lt_succ_iff, find_lt_iff]
