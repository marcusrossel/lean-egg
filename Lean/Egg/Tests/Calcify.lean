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
    _ = f 2 1 := (h 2 1).symm
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

-- This used to fail because we didn't correctly reduce and introduce variables before calling
-- calcify.
/--
info: Try this: ⏎
  intro a b
  calc
    f a a
    _ = f b a := h a b
-/
#guard_msgs in
example (h : ∀ x y : Nat, f x x = f y x) : ∀ a b : Nat, f a a = f b a := by
  egg? [h]


abbrev E := ∀ a b : Nat, f a a = f b a

/--
info: Try this: ⏎
  intro a b
  calc
    f a a
    _ = f b a := h a b
-/
#guard_msgs in
example (h : ∀ x y : Nat, f x x = f y x) : E f := by
  egg? [h]
