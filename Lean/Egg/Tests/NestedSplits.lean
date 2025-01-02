import Egg
open scoped Egg

set_option egg.genNestedSplits true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] a = b ↔ c = d
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (2)
    [egg.rewrites] #0⁅→⁆(⇔)
      [egg.rewrites] c = d
      [egg.rewrites] Conditions
        [egg.rewrites] a = b
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] #0⁅←⁆(⇔)
      [egg.rewrites] a = b
      [egg.rewrites] Conditions
        [egg.rewrites] c = d
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
set_option trace.egg.rewrites true in
egg_no_defeq in
set_option egg.builtins false in
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
