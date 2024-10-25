import Egg

-- This fails because we first apply `Prod.fst_correct` which joins the e-classes of `f` and
-- `(f, x).fst`. Thus, by our (necessarily) conservative approach to η-reduction, we can't reduce.

theorem Prod.fst_correct (a : α) (b : β) : (a, b).fst = a := rfl

set_option trace.egg true in
example (f : Nat → Nat) : (fun x => (f, x).fst x) = f := by
  egg [Prod.fst_correct]
