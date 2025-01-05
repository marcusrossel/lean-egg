import Egg
open scoped Egg

-- We used to have a bug where type class instance erasure blocked type class specialization,
-- because mvar collection was affected by the erasure and did not track instance mvars correctly.
-- This test checks that this isn't a problem anymore.

egg_no_defeq
set_option egg.builtins false
set_option egg.genTcProjRws false
set_option trace.egg.rewrites true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] -?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [.unconditionallyVisible], ?inst: [.inTcInstTerm, .isTcInst]]
      [egg.rewrites] RHS MVars
          [?x: [.unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.50 = ?m.50
      [egg.rewrites] LHS MVars
          [?m.50: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.50: [.unconditionallyVisible]]
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0<⊢>(⇔)
      [egg.rewrites] -?m.57 = ?m.57
      [egg.rewrites] LHS MVars
          [?m.57: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars [?m.57: [.unconditionallyVisible]]
-/
#guard_msgs(info) in
set_option egg.eraseTCInstances false in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] -?x = ?x
      [egg.rewrites] LHS MVars
          [?inst: [.inTcInstTerm, .isTcInst], ?x: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [.unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.123 = ?m.123
      [egg.rewrites] LHS MVars
          [?m.123: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.123: [.unconditionallyVisible]]
  [egg.rewrites] Definitional
    [egg.rewrites] Type Class Instances
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0<⊢>(⇔)
      [egg.rewrites] -?m.130 = ?m.130
      [egg.rewrites] LHS MVars
          [?m.130: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars [?m.130: [.unconditionallyVisible]]
-/
#guard_msgs(info) in
set_option egg.eraseTCInstances true in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  egg [h]

-- BUG: Goal type specialization should generate a rewrite here.
example (h : ∀ (α) [inst : Neg α] (x : α), @Neg.neg α inst x = x) : (0 : Int) = (0 : Int) := by
  sorry -- egg [h]
