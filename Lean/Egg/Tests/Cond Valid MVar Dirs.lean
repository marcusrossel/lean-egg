import Egg
open scoped Egg

-- This test ensures that condition mvars are correctly taken into account when determining the
-- valid direction of rewrites.

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): _h
      [egg.rewrites] f ?b = f ?a
      [egg.rewrites] Conditions
        [egg.rewrites] ?a = ?b
      [egg.rewrites] LHS MVars
          [?b: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?a: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0(⇐) by #0
      [egg.rewrites] f ?a = f ?b
      [egg.rewrites] Conditions
        [egg.rewrites] ?a = ?b
      [egg.rewrites] LHS MVars
          [?a: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?b: [unconditionallyVisible]]
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.builtins false in
set_option egg.groundEqs false in
egg_no_defeq in
example (f : Nat → Nat) (_h : ∀ a b : Nat, a = b → f b = f a) : true = true := by
  egg [_h]
