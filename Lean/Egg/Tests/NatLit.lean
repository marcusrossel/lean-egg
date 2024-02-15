import Egg

-- Tests involving conversions between `Nat.zero` and `Nat.succ _` and `.lit (.natVal _)`.

example : 0 = Nat.zero := by
  egg

example : 1 = Nat.succ 0 := by
  egg

example : Nat.succ 1 = Nat.succ (Nat.succ Nat.zero) := by
  egg

example : Int.ofNat (Nat.succ 1) = Int.ofNat (Nat.succ (Nat.succ Nat.zero)) := by
  egg

-- TODO: Add tests involving rewrites with Nat.succ or Nat.zero.
