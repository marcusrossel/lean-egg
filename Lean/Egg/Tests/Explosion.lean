import Egg

set_option egg.tcProjs false
set_option egg.builtins false
set_option egg.explosion true

variable (f : Nat → Nat → Nat)

set_option trace.egg.rewrites.explosion true

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.explosion] Explosion (0) -/
#guard_msgs in
example : true = true := by
  egg

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.explosion] Explosion (0) -/
#guard_msgs in
example (h : true = false) : true = false := by
  egg [h]

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.explosion] Explosion (0) -/
#guard_msgs in
example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  egg [h]

-- This should not generate exploded rewrites.
/-- trace: [egg.rewrites.explosion] Explosion (0) -/
#guard_msgs in
example (a b : Nat) (h : ∀ x y : Nat, f x y = f y x) : f a b = f b a := by
  egg [h]

-- This should generate two explosions of `h` - one for `a` and one for `b`.
/--
trace: [egg.rewrites.explosion] Explosion (2)
  [egg.rewrites.explosion] #0💥[3](⇒)
    [egg.rewrites.explosion] f ?m.285 ?m.285 = f a ?m.285
    [egg.rewrites.explosion] LHS MVars
        [?m.285: [unconditionallyVisible]]
    [egg.rewrites.explosion] RHS MVars
        [?m.285: [unconditionallyVisible]]
  [egg.rewrites.explosion] #0💥[4](⇒)
    [egg.rewrites.explosion] f ?m.294 ?m.294 = f b ?m.294
    [egg.rewrites.explosion] LHS MVars
        [?m.294: [unconditionallyVisible]]
    [egg.rewrites.explosion] RHS MVars
        [?m.294: [unconditionallyVisible]]
-/
#guard_msgs in
example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  egg [h]

set_option trace.egg.rewrites.explosion false

-- TODO: Egg finds a a broken proof paths: by rewriting `f #0 #0` with both `h₁` and `h₂` which
--       establishes `0 = f #0 #0 = 1`. Is there any sensible way to fix this?

set_option egg.explosion false in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  sorry -- egg [h₁, h₂]

set_option egg.explosion true in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]
