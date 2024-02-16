import Egg

-- Tests for manually inspecting what terms look like with or without constant level erasure.
set_option trace.egg true

-- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unify.20level.20mvars
example : 0 = 0 := by
  egg (config := { eraseConstLevels := true })

example : 0 = 0 := by
  egg (config := { eraseConstLevels := false })
