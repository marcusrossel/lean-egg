import Egg

-- This fails because we with intersection semantics η-reduction is applied before applying
-- `first_correct` which yields open terms in the explanation.

set_option egg.unionSemantics false

def first (a : α) (_ : β) : α := a

theorem first_correct (a : α) (b : β) : first a b = a := rfl

example (f : α → α) : (fun x => (first f x) x) = f := by
  sorry -- egg [first_correct]

example : (fun (z : α → α → α) x => (fun _y => z) x x) = (fun x => x) := by
  sorry -- egg
