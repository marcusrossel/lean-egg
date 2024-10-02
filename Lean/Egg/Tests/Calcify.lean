import Egg

/--
info: Try this: calc
    true
    _ = true := Eq.refl true
-/
#guard_msgs in
example : true = true := by
  egg?

/--
info: Try this: calc
    a
    _ = b := h₁
    _ = c := h₂
-/
#guard_msgs in
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg? [h₁, h₂]

variable (f : Nat → Nat → Nat)

/--
info: Try this: calc
    f 1 2
    _ = f 2 1 := Eq.symm (h 2 1)
-/
#guard_msgs in
example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  egg? [h]

/--
info: Try this: calc
    f a a
    _ = f b a := h a b
-/
#guard_msgs in
example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  egg? [h]
