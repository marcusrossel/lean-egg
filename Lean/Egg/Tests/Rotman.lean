import Egg

@[simp]
def Nat.choose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem Nat.choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
  | _,     0,     h => absurd h (Nat.not_lt_zero _)
  | 0,     k + 1, _ => rfl
  | n + 1, k + 1, h => by
    have h₁ : n < k     := by omega
    have h₂ : n < k + 1 := by omega
    simp [choose_eq_zero_of_lt h₁, choose_eq_zero_of_lt h₂]

theorem Nat.choose_self (n : Nat) : n.choose n = 1 := by
  induction n
  case zero   => rfl
  case succ h => simp [h, choose_eq_zero_of_lt]

@[simp]
def Nat.factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => Nat.factorial n

theorem proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r := by sorry

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => rw [Nat.le_zero.mp h]; rfl
  case succ n hi =>
    by_cases hr : r = 0 <;> try subst hr
    case pos =>
      replace h : 0 < (n + 1) * (n !) := by sorry -- by h and factorial always > 0
      simp [Nat.div_self h]
    case neg =>
      by_cases hn : r = n + 1 <;> try subst hn
      case pos =>
        replace h : 0 < (n + 1) * (n !) := by sorry -- by hr and factorial always > 0
        simp [-Nat.choose, Nat.choose_self, Nat.div_self h]
      case neg =>
        have h₁ : n ≥ r - 1               := by omega
        have h₂ : n ≥ r                   := by omega
        have h₃ : n - (r - 1) = n - r + 1 := by omega
        calc
          _ = n.choose (r - 1) + n.choose r                                                  := proposition_1_14 ..
          _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)                   := by rw [hi h₁, hi h₂, h₃]

          _ = (n !) / ((r - 1)! * (n - r)! * (n - r + 1)) + (n !) / (r ! * (n - r)!)         := by egg [Nat.factorial, Nat.mul_assoc, Nat.mul_comm]
          _ = ((n !) / ((r - 1)! * (n - r)!)) * (1 / (n - r + 1)) + (n !) / (r ! * (n - r)!) := sorry

          _ = (n !) / ((r - 1)! * (n - r)!) * (1 / (n - r + 1) + 1 / r)                      := by sorry
          _ = (n !) / ((r - 1)! * (n - r)!) * ((r + n - r + 1) / (r * (n - r + 1)))          := by sorry
          _ = (n !) / ((r - 1)! * (n - r)!) * ((n + 1) / (r * (n - r + 1)))                  := by egg [Nat.add_comm, Nat.add_sub_cancel]
          _ = (n + 1)! / (r ! * (n + 1 - r)!)                                                := by sorry -- div_mul_div_comm requires that ((r - 1)! * (n - r)!) divides (n !) and (r * (n - r + 1)) divides (n + 1)
