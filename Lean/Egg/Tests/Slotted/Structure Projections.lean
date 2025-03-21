import Egg

structure S where
  s : Nat
  t : Bool

example : S.s = S.s := by
  egg

example : S.mk = S.mk := by
  egg

example : S.mk 1 = S.mk 1 := by
  egg

example : S.s (S.mk 1 false) = S.s (S.mk 1 false) := by
  egg

example :
    { s := 2, t := false : S }.s + { s := 1, t := false : S }.s =
    { s := 1, t := false : S }.s + { s := 2, t := false : S }.s := by
  egg

example : (0, 1) = (0, 1) := by
  egg

example : Prod.mk α β = Prod.mk α β := by
  egg
