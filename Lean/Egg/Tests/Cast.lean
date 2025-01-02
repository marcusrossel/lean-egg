import Egg

namespace Simple

class C (α) extends NatCast α, Add α

variable (cast_add : ∀ {R} [C R] (m n : Nat), ((m + n : Nat) : R) = m + n)

example (a b : Nat) [C R] : Nat.cast (a + b) = (a : R) + b := by
  egg [cast_add]

instance : C Int where

set_option trace.egg true in
example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  egg [cast_add]

end Simple

namespace NoDiamond

class N (R) extends NatCast R, Add R where

variable (cast_add : ∀ {R : Type _} [N R] (m n : Nat), ((m + n : Nat) : R) = m + n)

example (a b : Nat) [N R] : Nat.cast (a + b) = (a : R) + b := by
  egg [cast_add]

instance : N Int where

example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  egg [cast_add]

end NoDiamond

namespace Diamond

class A (α) extends Add α where
class B (α) extends Add α where
class N (R) extends NatCast R, A R, B R where

variable (cast_add : ∀ {R} [N R] (m n : Nat), ((m + n : Nat) : R) = m + n)

example (a b : Nat) [N R] : Nat.cast (a + b) = (a : R) + b := by
  egg [cast_add]

instance : N Int where

example (a b : Nat) : Nat.cast (a + b) = (a : Int) + b := by
  egg [cast_add]

end Diamond
