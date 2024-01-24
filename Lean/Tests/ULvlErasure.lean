import Egg

-- Tests for manually inspecting what terms look like with or without universe level erasure.
set_option trace.egg true

-- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unify.20level.20mvars
example : 0 = 0 := by
  egg (config := { eraseULvls := true })

example : 0 = 0 := by
  egg (config := { eraseULvls := false })
