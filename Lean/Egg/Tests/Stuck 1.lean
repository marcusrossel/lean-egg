import Egg

-- This used to get stuck due to missing bvar e-class analyses for the subst and shift constructs.

theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
  a[i] = a[i.val] := rfl

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
example (a : Array α) {i j : Fin a.size} : a[i] = a[j] := by
  egg [getElem_fin]
