import Egg

structure S where
  s : Nat

example : S.s = S.s := by
  egg

example : S.mk = S.mk := by
  egg

example : S.mk 1 = S.mk 1 := by
  egg

example : S.s (S.mk 1) = S.s (S.mk 1) := by
  egg

example : { s := 2 : S }.s + { s := 1 : S }.s = { s := 1 : S }.s + { s := 2 : S }.s := by
  egg

example : (0, 1) = (0, 1) := by
  egg

example : Prod.mk α β = Prod.mk α β := by
  egg
