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

example (h : ∀ n, Nat.succ n = n + 1) : 1 = Nat.zero + 1 := by
  egg [h]

-- TODO: Add more tests involving rewrites with Nat.succ or Nat.zero.
