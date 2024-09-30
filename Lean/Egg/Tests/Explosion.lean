import Egg

set_option egg.genEtaRw false
set_option egg.genBetaRw false
set_option egg.genTcProjRws false
set_option egg.genGoalTcSpec false
set_option egg.builtins false
set_option egg.genNatLitRws false

set_option egg.explosion true

variable (f : Nat → Nat → Nat)

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Generated (0)
  [egg.rewrites] Exploded (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Hypotheses (0)
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
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] true = false
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Generated (0)
  [egg.rewrites] Exploded (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Hypotheses (0)
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
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] f ?x ?y = f ?y ?x
      [egg.rewrites] LHS MVars
          expr:  [?y, ?x]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?y, ?x]
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Generated (0)
  [egg.rewrites] Exploded (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example (h : ∀ x y : Nat, f x y = f y x) : f 1 2 = f 2 1 := by
  egg [h]

-- This should not generate exploded rewrites.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] f ?x ?y = f ?y ?x
      [egg.rewrites] LHS MVars
          expr:  [?y, ?x]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?y, ?x]
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Generated (0)
  [egg.rewrites] Exploded (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example (a b : Nat) (h : ∀ x y : Nat, f x y = f y x) : f a b = f b a := by
  egg [h]

-- This should generate two explosions of `h` - one for `a` and one for `b`.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇐): h
      [egg.rewrites] f ?x ?x = f ?y ?x
      [egg.rewrites] LHS MVars
          expr:  [?x]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?x, ?y]
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Generated (0)
  [egg.rewrites] Exploded (2)
    [egg.rewrites] #0💥→[3](⇔)
      [egg.rewrites] f ?m.272 ?m.272 = f a ?m.272
      [egg.rewrites] LHS MVars
          expr:  [?m.272]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?m.272]
          class: []
          level: []
    [egg.rewrites] #0💥→[4](⇔)
      [egg.rewrites] f ?m.281 ?m.281 = f b ?m.281
      [egg.rewrites] LHS MVars
          expr:  [?m.281]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?m.281]
          class: []
          level: []
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example (a b : Nat) (h : ∀ x y : Nat, f x x = f y x) : f a a = f b a := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.explosion false in
example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]

example (a : Nat) (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]

example (a : Nat) (h₁ : ∀ x : Nat, 0 = f x x) (h₂ : ∀ x : Nat, 1 = f x x) : 0 = 1 := by
  egg [*]

-- TODO: Should we add an exploded rewrite for `Inhabited.default` when the local context doesn't
--       contain a term of the required type?
/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h₁ : ∀ x : Nat, f x x = 0) (h₂ : ∀ x : Nat, f x x = 1) : 0 = 1 := by
  egg [h₁, h₂]
