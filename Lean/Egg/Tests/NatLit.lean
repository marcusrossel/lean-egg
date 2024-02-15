import Egg

-- Tests involving conversions between `Nat.zero` and `Nat.succ _` and `.lit (.natVal _)`.

-- TODO: https://github.com/marcusrossel/lean-egg/issues/11
example : 0 = Nat.zero := by
  egg
