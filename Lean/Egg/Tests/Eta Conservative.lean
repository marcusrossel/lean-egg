import Egg

-- This fails because we first apply `first_correct` which joins the e-classes of `f` and
-- `first f x`. Thus, by our (necessarily) conservative approach to η-reduction, we can't reduce.

def first (a : α) (_ : β) : α := a

theorem first_correct (a : α) (b : β) : first a b = a := rfl

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (f : α → α) : (fun x => (first f x) x) = f := by
  egg [first_correct]
