import Egg
open scoped Egg

egg_no_defeq
set_option egg.genTcProjRws false
set_option egg.genGoalTcSpec false
set_option egg.builtins false

set_option egg.explosion true

variable (f : Nat → Nat → Nat)

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example : true = true := by
  egg

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] true = false
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example (h : true = false) : true = false := by
  egg [h]

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] f ?x ?y = f ?y ?x
      [egg.rewrites] LHS MVars
          [?y: [unconditionallyVisible], ?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?y: [unconditionallyVisible], ?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.genGroundEqs false in
example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  egg [h]

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] f ?x ?y = f ?y ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible], ?y: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible], ?y: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.genGroundEqs false in
example (a b : Nat) (h : ∀ x y : Nat, f x y = f y x) : f a b = f b a := by
  egg [h]

-- This should generate two explosions of `h` - one for `a` and one for `b`.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇐): h
      [egg.rewrites] f ?x ?x = f ?y ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?y: [unconditionallyVisible], ?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (2)
    [egg.rewrites] #0💥→[3](⇔)
      [egg.rewrites] f ?m.235 ?m.235 = f a ?m.235
      [egg.rewrites] LHS MVars
          [?m.235: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.235: [unconditionallyVisible]]
    [egg.rewrites] #0💥→[4](⇔)
      [egg.rewrites] f ?m.244 ?m.244 = f b ?m.244
      [egg.rewrites] LHS MVars
          [?m.244: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.244: [unconditionallyVisible]]
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.genGroundEqs false in
example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  egg [h]

-- BUG: Egg finds a a broken proof path: by rewriting `f #0 #0` with both `h₁` and `h₂` which
--      establishes `0 = f #0 #0 = 1`. Is there any sensible way to fix this?
set_option egg.explosion false in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  sorry -- egg [h₁, h₂]

example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]

example (a : Nat) (h₁ : ∀ x : Nat, 0 = f x x) (h₂ : ∀ x : Nat, 1 = f x x) : 0 = 1 := by
  egg [*]
