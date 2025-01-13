import Egg
open scoped Egg

-- These tests show how type class specialization is applied to conditions of conditional rewrites.

set_option egg.eraseTCInstances false
egg_no_defeq
set_option egg.builtins false
set_option egg.genGroundEqs false
set_option egg.genGoalTcSpec false
set_option egg.genTcSpecRws false
set_option egg.genTcSpecRws true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] p = q
      [egg.rewrites] Conditions
        [egg.rewrites] Decidable p
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<?>(⇔)
      [egg.rewrites] p = q
      [egg.rewrites] Conditions
        [egg.rewrites] Proven
          [egg.rewrites] Decidable p
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  egg [h]
