import Egg

set_option egg.genNestedSplits true

/--
warning: unused variable `h`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] a = b ↔ c = d
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
  [egg.rewrites] Split Nested (2)
    [egg.rewrites] #0⁅→⁆(⇔)
      [egg.rewrites] c = d
      [egg.rewrites] Conditions
        [egg.rewrites] a = b
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
    [egg.rewrites] #0⁅←⁆(⇔)
      [egg.rewrites] a = b
      [egg.rewrites] Conditions
        [egg.rewrites] c = d
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
  [egg.rewrites] Type Class (0)
  [egg.rewrites] Explosion (0)
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.builtins false in
set_option egg.beta false in
set_option egg.eta false in
set_option egg.natLit false in
set_option egg.levels false in
set_option egg.eraseProofs false in
set_option egg.eraseTCInstances false in
set_option egg.genTcProjRws false in
example (h : (a = b) ↔ (c = d)) : 0 = 0 := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.genNestedSplits false in
example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) : c = d := by
  egg [h₁, h₂]

example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) : c = d := by
  egg [h₁, h₂]

example (h₁ : (a = b) ↔ (c = d)) (h₂ : c = d) : a = b := by
  egg [h₁, h₂]

example (h₁ : (a = b) ↔ (c = d)) (h₂ : a = b) (h₃ : d = e) : c = e := by
  egg [h₁, h₂, h₃]
