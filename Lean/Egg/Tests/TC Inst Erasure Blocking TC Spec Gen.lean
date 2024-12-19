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
          [?inst: [.inTcInstTerm, .isTcInst], ?x: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [.unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.38 = ?m.38
      [egg.rewrites] LHS MVars
          [?m.38: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.38: [.unconditionallyVisible]]
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
set_option egg.eraseTCInstances false in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : true = true := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] -?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [.unconditionallyVisible], ?inst: [.inTcInstTerm, .isTcInst]]
      [egg.rewrites] RHS MVars
          [?x: [.unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.86 = ?m.86
      [egg.rewrites] LHS MVars
          [?m.86: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.86: [.unconditionallyVisible]]
  [egg.rewrites] Definitional
    [egg.rewrites] Type Class Instances
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
set_option egg.eraseTCInstances true in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : true = true := by
  egg [h]
