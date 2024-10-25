import Egg

-- This used to crash, before we changed proof erasure to encode the type of propositions.

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
example (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  egg [set, Array.getElem_eq_toList_getElem, List.getElem_set_ne h]
