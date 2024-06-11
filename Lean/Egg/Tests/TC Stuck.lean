import Egg

-- This test checks that equations of definitions involving type classes are correctly elaborated.
-- This previously failed with `typeclass instance problem is stuck, it is often due to metavariables`.

def f [Inhabited α] : α := Inhabited.default

example : 0 = 0 := by
  egg [f]
