import Mathlib
import Egg

-- https://github.com/marcusrossel/lean-egg/issues/43#issue-2683081133
example {a : Nat} : 2 * a = a + a :=by
  egg [two_mul]
