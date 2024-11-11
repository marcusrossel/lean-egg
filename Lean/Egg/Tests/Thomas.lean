import Egg

-- This used to not terminate with union semantics, before we introduced a cutoff to the loose bvar
-- e-class analysis.

-- TODO: Why does this fail?
set_option egg.unionSemantics true in
example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun _y => (fun z => z) := by
  sorry -- egg

set_option egg.unionSemantics false in
example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun _y => (fun z => z) := by
  egg
