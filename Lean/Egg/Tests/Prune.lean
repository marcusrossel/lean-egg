import Egg
open scoped Egg

-- These test check that redundant rewrites are pruned.

egg_no_defeq
set_option egg.genTcProjRws false
set_option egg.genGroundEqs false
set_option egg.builtins false

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h₁
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (3)
    [egg.rewrites] #0(⇐) by #0
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] #1(⇒) by #0
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] #1(⇐) by #0
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars []
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option trace.egg.rewrites true in
example (h₁ h₂ : 0 = 0) : 0 = 0 := by
  egg [h₁, h₂]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): Nat.add_comm
      [egg.rewrites] ?n + ?m = ?m + ?n
      [egg.rewrites] LHS MVars
          [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (3)
    [egg.rewrites] #0(⇐) by #0
      [egg.rewrites] ?m + ?n = ?n + ?m
      [egg.rewrites] LHS MVars
          [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
    [egg.rewrites] #1(⇒) by #0
      [egg.rewrites] ?a + ?b = ?b + ?a
      [egg.rewrites] LHS MVars
          [?a: [unconditionallyVisible], ?b: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?a: [unconditionallyVisible], ?b: [unconditionallyVisible]]
    [egg.rewrites] #1(⇐) by #0
      [egg.rewrites] ?b + ?a = ?a + ?b
      [egg.rewrites] LHS MVars
          [?a: [unconditionallyVisible], ?b: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars [?a: [unconditionallyVisible], ?b: [unconditionallyVisible]]
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option trace.egg.rewrites true in
example (h : ∀ a b : Nat, a + b = b + a) : 0 = 0 := by
  egg [Nat.add_comm, h]
