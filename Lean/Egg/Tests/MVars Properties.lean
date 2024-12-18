import Egg
open scoped Egg

egg_no_defeq
set_option egg.builtins false
set_option egg.genTcProjRws false
set_option trace.egg.rewrites true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [.inTarget]]
      [egg.rewrites] RHS MVars
          [?x: [.inTarget]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (h : ∀ x : Nat, x = x) : true = true := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] f ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [.inTarget], ?α: [.inTarget]]
      [egg.rewrites] RHS MVars
          [?x: [.inTarget]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (f : {α : Type} → α → α) (h : ∀ α (x : α), f x = x) : true = true := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] ?x + ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [.inTarget], ?inst✝: [.inTcInstTerm, .isTcInst, .inTarget]]
      [egg.rewrites] RHS MVars
          [?x: [.inTarget]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (h : ∀ [Add α] (x : α), x + x = x) : true = true := by
  egg [h]
