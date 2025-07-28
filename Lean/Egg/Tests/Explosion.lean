import Egg
open scoped Egg

set_option egg.tcProjs false
set_option egg.builtins false
set_option egg.explosion true

variable (f : Nat → Nat → Nat)

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.derived] Derived (0) -/
#guard_msgs in
set_option trace.egg.rewrites.derived true in
example : true = true := by
  egg

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.derived] Derived (0) -/
#guard_msgs in
set_option trace.egg.rewrites.derived true in
example (h : true = false) : true = false := by
  egg [h]

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.derived] Derived (0) -/
#guard_msgs in
set_option trace.egg.rewrites.derived true in
set_option egg.groundEqs false in
example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  egg [h]

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.derived] Derived (0) -/
#guard_msgs in
set_option trace.egg.rewrites.derived true in
set_option egg.groundEqs false in
example (a b : Nat) (h : ∀ x y : Nat, f x y = f y x) : f a b = f b a := by
  egg [h]

-- This should generate two explosions of `h` - one for `a` and one for `b`.
/--
trace: [egg.rewrites.derived] Derived (2)
  [egg.rewrites.derived] #0💥[3](⇒)
    [egg.rewrites.derived] f ?m.243 ?m.243 = f a ?m.243
    [egg.rewrites.derived] LHS MVars
        [?m.243: [unconditionallyVisible]]
    [egg.rewrites.derived] RHS MVars
        [?m.243: [unconditionallyVisible]]
  [egg.rewrites.derived] #0💥[4](⇒)
    [egg.rewrites.derived] f ?m.252 ?m.252 = f b ?m.252
    [egg.rewrites.derived] LHS MVars
        [?m.252: [unconditionallyVisible]]
    [egg.rewrites.derived] RHS MVars
        [?m.252: [unconditionallyVisible]]
-/
#guard_msgs in
set_option trace.egg.rewrites.derived true in
set_option egg.groundEqs false in
example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  egg [h]

-- TODO: Egg finds a a broken proof paths: by rewriting `f #0 #0` with both `h₁` and `h₂` which
--       establishes `0 = f #0 #0 = 1`. Is there any sensible way to fix this?

set_option egg.explosion false in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  sorry -- egg [h₁, h₂]

set_option egg.explosion true in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]
