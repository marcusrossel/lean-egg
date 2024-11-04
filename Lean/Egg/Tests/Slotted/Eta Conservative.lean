import Egg

set_option egg.slotted true

def first (a : α) (_ : β) : α := a

theorem first_correct (a : α) (b : β) : first a b = a := rfl

example (f : α → α) : (fun x => (first f x) x) = f := by
  egg [first_correct]

example : (fun (z : α → α → α) x => (fun _y => z) x x) = (fun x => x) := by
  egg
