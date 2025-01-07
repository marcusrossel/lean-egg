import Egg

-- These tests show how type class specialization is applied to conditions of conditional rewrites.

-- /-- error: egg failed to prove the goal (saturated) -/
-- #guard_msgs in
set_option egg.genTcSpecRws false in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  sorry -- egg [h]

set_option trace.egg true
set_option egg.genTcSpecRws false in
set_option egg.builtins false in
set_option egg.derivedGuides false in
example [Decidable p] (h : [Decidable p] → p = q) : p = q := by
  egg [h]

set_option egg.genTcSpecRws true in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  sorry -- egg [h]
