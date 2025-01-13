import Egg

-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/unification.20problem.20in.20rw/near/438497625

variable {α} {f : α → α → α} (f_comm : ∀ a b, f a b = f b a) (f_assoc : ∀ a b c, f (f a b) c = f a (f b c))

include f_assoc f_comm in
theorem foldl_descend : (head :: tail).foldl f init = f init (tail.foldl f head) := by
  induction tail generalizing init <;> egg [List.foldl, *]

include f_assoc f_comm in
theorem foldl_eq_foldr (l : List α) : l.foldl f init = l.foldr f init := by
  induction l <;> egg [List.foldl, List.foldr, foldl_descend, *]
