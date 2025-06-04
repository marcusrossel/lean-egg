import Egg

attribute [egg nat] Nat.add_mul Nat.one_mul Nat.add_assoc Nat.zero_mul Nat.add_zero Nat.add_comm

inductive Vect (α : Type _) : Nat → Type _ where
  | nil  : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

namespace Vect

def drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0,     v        => v
  | n + 1, cons _ r => drop n r

def take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0,     _        => nil
  | n + 1, cons h r => cons h (take n r)

def cast (xs : Vect α n) (h : n = m := by egg +nat) : Vect α m :=
  h ▸ xs

def slide (sz sp : Nat) (xs : Vect α <| sz + n * (sp + 1)) : Vect (Vect α sz) (n + 1) :=
  match n with
  | 0 => cons xs.cast nil
  | m + 1 =>
    let window := xs.cast.take sz (k := (m + 1) * (sp + 1))
    let rem    := slide sz sp <| xs.cast.drop <| sp + 1
    cons window rem
