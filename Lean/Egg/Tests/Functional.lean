import Egg

-- Tests involving basic functional programming.
namespace Functional

inductive List α
  | nil : List α
  | cons : α → List α → List α

def append : List α → List α → List α
  | .nil,       bs => bs
  | .cons a as, bs => .cons a (append as bs)

theorem append_nil (as : List α) : append as .nil = as := by
  induction as with
  | nil         => egg [append]
  | cons _ _ ih => egg [ih, append]

-- Note: This test contains universe parameters.
theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil         => egg [append]
  | cons _ _ ih => egg [ih, append]

def reverseAux : List α → List α → List α
  | .nil,      r => r
  | .cons a l, r => reverseAux l (.cons a r)

def reverse (as : List α) : List α :=
  reverseAux as .nil

theorem reverseAux_eq_append (as bs : List α) :
    reverseAux as bs = append (reverseAux as .nil) bs := by
  induction as generalizing bs with
  | nil         => egg [reverseAux, append]
  | cons _ _ ih => egg [reverseAux, append_assoc, ih, append]

theorem reverse_nil : reverse (.nil : List α) = .nil := by
  egg [reverse, reverseAux]

theorem reverse_cons (a : α) (as : List α) :
    reverse (.cons a as) = append (reverse as) (.cons a .nil) := by
  egg [reverse, reverseAux, reverseAux_eq_append]

theorem reverse_append (as bs : List α) :
    reverse (append as bs) = append (reverse bs) (reverse as) := by
  induction as generalizing bs with
  | nil          => egg [reverse_nil, append_nil, append]
  | cons a as ih => egg [ih, append_assoc, reverse_cons, append]

def map (f : α → β) : List α → List β
  | .nil       => .nil
  | .cons a as => .cons (f a) (map f as)

def foldr (f : α → β → β) (init : β) : List α → β
  | .nil      => init
  | .cons a l => f a (foldr f init l)

def all (p : α → Bool) (xs : List α) : Bool :=
  foldr and true (map p xs)

def all' (p : α → Bool) : List α → Bool
  | .nil       => true
  | .cons x xs => (p x) && (all' p xs)

theorem all_deforestation (p : α → Bool) (xs : List α) : all p xs = all' p xs := by
  induction xs with
  | nil         => /-simp [all, all', foldr, map, ih]-/ egg [all, all', foldr, map]
  | cons _ _ ih => try simp [all, all', foldr, map, ih]; egg [all, all', foldr, map, ih]
