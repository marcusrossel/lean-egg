import Egg

-- These test check that redundant rewrites are pruned.

-- TODO: Add a macro to turn off all defeqs.
set_option egg.genTcProjRws false
set_option egg.builtins false
set_option egg.beta false
set_option egg.eta false
set_option egg.natLit false
set_option egg.levels false
set_option egg.eraseProofs false
set_option egg.eraseTCInstances false

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h₁
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #1(⇔)
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option trace.egg.rewrites true in
example (h₁ h₂ : 0 = 0) : 0 = 0 := by
  egg [h₁, h₂]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): Nat.add_comm
      [egg.rewrites] ?n + ?m = ?m + ?n
      [egg.rewrites] LHS MVars
          expr:  [?m, ?n]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?m, ?n]
          class: []
          level: []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Split Nested (0)
  [egg.rewrites] Type Class (0)
  [egg.rewrites] Explosion (0)
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #1(⇔)
      [egg.rewrites] ?a + ?b = ?b + ?a
      [egg.rewrites] LHS MVars
          expr:  [?a, ?b]
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  [?a, ?b]
          class: []
          level: []
-/
#guard_msgs in
set_option linter.unusedVariables false in
set_option trace.egg.rewrites true in
example (h : ∀ a b : Nat, a + b = b + a) : 0 = 0 := by
  egg [Nat.add_comm, h]
