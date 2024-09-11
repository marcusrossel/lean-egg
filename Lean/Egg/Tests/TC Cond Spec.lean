import Egg

-- These tests show how type class specialization is applied to conditions of conditional rewrites.

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.genTcSpecRws false in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  egg [h]

set_option egg.genTcSpecRws false in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  egg [h; inst]

set_option egg.genTcSpecRws true in
example [inst : Decidable p] (h : [Decidable p] → p = q) : p = q := by
  egg [h]
