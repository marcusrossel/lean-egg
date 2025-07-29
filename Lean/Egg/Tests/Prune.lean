import Egg

-- These test check that redundant rewrites are pruned.

set_option trace.egg.rewrites.pruned true
set_option linter.unusedVariables false

/--
trace: [egg.rewrites.pruned] Pruned (3)
  [egg.rewrites.pruned] #0(⇐) by #0
    [egg.rewrites.pruned] 0 = 0
    [egg.rewrites.pruned] LHS MVars
        []
    [egg.rewrites.pruned] RHS MVars
        []
  [egg.rewrites.pruned] #1(⇒) by #0
    [egg.rewrites.pruned] 0 = 0
    [egg.rewrites.pruned] LHS MVars
        []
    [egg.rewrites.pruned] RHS MVars
        []
  [egg.rewrites.pruned] #1(⇐) by #0
    [egg.rewrites.pruned] 0 = 0
    [egg.rewrites.pruned] LHS MVars
        []
    [egg.rewrites.pruned] RHS MVars
        []
-/
#guard_msgs in
example (h₁ h₂ : 0 = 0) : 0 = 0 := by
  egg [h₁, h₂]

/--
trace: [egg.rewrites.pruned] Pruned (4)
  [egg.rewrites.pruned] #0(⇐) by #0
    [egg.rewrites.pruned] ?m + ?n = ?n + ?m
    [egg.rewrites.pruned] LHS MVars
        [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
    [egg.rewrites.pruned] RHS MVars
        [?m: [unconditionallyVisible], ?n: [unconditionallyVisible]]
  [egg.rewrites.pruned] #1(⇒) by #0
    [egg.rewrites.pruned] ?a + ?b = ?b + ?a
    [egg.rewrites.pruned] LHS MVars
        [?b: [unconditionallyVisible], ?a: [unconditionallyVisible]]
    [egg.rewrites.pruned] RHS MVars
        [?b: [unconditionallyVisible], ?a: [unconditionallyVisible]]
  [egg.rewrites.pruned] #1(⇐) by #0
    [egg.rewrites.pruned] ?b + ?a = ?a + ?b
    [egg.rewrites.pruned] LHS MVars
        [?b: [unconditionallyVisible], ?a: [unconditionallyVisible]]
    [egg.rewrites.pruned] RHS MVars
        [?b: [unconditionallyVisible], ?a: [unconditionallyVisible]]
  [egg.rewrites.pruned] #1↓(⇒) by #0↓
    [egg.rewrites.pruned] ∀ (a b : Nat), a + b = b + a = True
    [egg.rewrites.pruned] LHS MVars
        []
    [egg.rewrites.pruned] RHS MVars
        []
-/
#guard_msgs in
example (h : ∀ a b : Nat, a + b = b + a) : 0 = 0 := by
  egg [Nat.add_comm, h]
