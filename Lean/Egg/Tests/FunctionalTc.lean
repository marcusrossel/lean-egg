import Egg

-- Tests involving auto-generated rewrite rules for reducing type class projections.
namespace TcProj

inductive List (α) where
  | nil : List α
  | cons : α → List α → List α

notation "[]" => List.nil
infixr:50 " :: " => List.cons

def append : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: (append as bs)

instance {α : Type _} : Append (List α) where
  append := append

theorem append_nil (as : List α) : as ++ [] = as := by
  induction as with
  | nil         => egg [append]
  | cons _ _ ih => egg [ih, append]

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil         => egg [append]
  | cons _ _ ih => egg [ih, append]

def reverseAux : List α → List α → List α
  | [],     r => r
  | a :: l, r => reverseAux l (a :: r)

def reverse (as : List α) : List α :=
  reverseAux as []

theorem reverseAux_eq_append (as bs : List α) : reverseAux as bs = (reverseAux as []) ++ bs := by
  induction as generalizing bs with
  | nil         => egg [reverseAux, append]
  | cons _ _ ih => egg [reverseAux, append_assoc, ih, append]

theorem reverse_nil : reverse ([] : List α) = [] := by
  egg [reverse, reverseAux]

theorem reverse_cons (a : α) (as : List α) : reverse (a :: as) = (reverse as) ++ (a :: []) := by
  egg [reverse, reverseAux, reverseAux_eq_append]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil          => egg [reverse_nil, append_nil, append]
  | cons a as ih => egg [ih, append_assoc, reverse_cons, append]
