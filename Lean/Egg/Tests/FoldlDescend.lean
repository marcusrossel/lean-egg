import Egg

-- Tests based on https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/unification.20problem.20in.20rw/near/438497625
theorem foldl_descend {f : α → α → α}
    {f_comm : ∀ a b : α, f a b = f b a}
    {f_assoc : ∀ a b c : α, f (f a b) c = f a (f b c)} :
    List.foldl f init (head :: tail) = f init (List.foldl f head tail) := by
  induction tail generalizing init with
  | nil => rfl
  | cons h₂ tail ih => egg [List.foldl, f_assoc, f_comm, ih]

theorem foldl_eq_foldr
    {f : α → α → α}
    {f_comm : ∀ a b : α, f a b = f b a}
    {f_assoc : ∀ a b c : α, f (f a b) c = f a (f b c)} :
    List.foldl f init l = List.foldr f init l := by
  induction l with
  | nil => rfl
  | cons ha l ih =>
    conv => rhs; unfold List.foldr; rw [f_comm, ←ih]
    conv => lhs; unfold List.foldl
    cases l with
    | nil => rfl
    | cons hb tail => egg [@foldl_descend _ _ _ _ _ f_comm f_assoc, f_assoc, f_comm]
