import Egg

-- This tests checks that `egg` can be the final syntax in a file without throwing the error
-- "Unexpected end of input".

example : 0 = 0 := by
  egg (config := { })
