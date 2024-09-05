import Egg

theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
  a[i] = a[i.val] := rfl

-- BUG: The `gt_iff_lt` builtin rewrite is somehow related to this.
-- NOTE: This is unrelated to proof erasure.
set_option egg.genBetaRw true in
-- turning off eta also fixes it
set_option egg.genTcProjRws true in
set_option egg.builtins true in
set_option trace.egg true in
example (a : Array α) {i j : Fin a.size} : a[i] = a[j] := by
  sorry -- egg [getElem_fin]
