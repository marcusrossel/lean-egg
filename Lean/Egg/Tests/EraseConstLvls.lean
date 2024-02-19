import Egg

-- Tests for manually inspecting what terms look like with or without constant level erasure.

-- BUG: proof reconstruction
example : 0 = 0 := by
  egg (config := { eraseConstLevels := true })

example : 0 = 0 := by
  egg (config := { eraseConstLevels := false })
