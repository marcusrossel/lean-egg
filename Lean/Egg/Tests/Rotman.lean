import Egg

-- From Mathlib
axiom Nat.div_mul_div_comm {a b c d : Nat} : b ∣ a → d ∣ c → (a / b) * (c / d) = (a * c) / (b * d)

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

-- From Mathlib
axiom Nat.mul_factorial_pred {n : Nat} (hn : 0 < n) : n * (n - 1)! = n !

-- From Rotman
axiom proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r

theorem todo {n : Nat} (h : n ≥ r) : (n - r) + k = (n + k) - r := sorry

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
        have h₁ : n ≥ r - 1                     := by omega
        have h₂ : n ≥ r                         := by omega
        have h₃ : n - (r - 1) = n - r + 1       := by omega
        have h₄ : ((r - 1)! * (n - r)!) ∣ (n !) := sorry
        have h₅ : (r * (n - r + 1)) ∣ (n  + 1)  := sorry
        have h₆ : 0 < r                         := by omega

        -- These calculations have to be done over the rationals:
        have h₇ := calc (n !) / ((r - 1)! * (n - r)! * (n - r + 1)) + (n !) / (r ! * (n - r)!)
          _ = ((n !) / ((r - 1)! * (n - r)!)) * (1 / (n - r + 1)) + (n !) / (r ! * (n - r)!) := sorry
          _ = (n !) / ((r - 1)! * (n - r)!) * (1 / (n - r + 1) + 1 / r)                      := sorry
          _ = (n !) / ((r - 1)! * (n - r)!) * ((r + n - r + 1) / (r * (n - r + 1)))          := sorry

        calc (n + 1).choose r
          _ = (n !) / ((r - 1)! * (n - r)! * (n - r + 1)) + (n !) / (r ! * (n - r)!) := by egg [proposition_1_14, hi, h₃, Nat.factorial, Nat.mul_assoc, Nat.mul_comm; h₁, h₂]
          _ = (n !) / ((r - 1)! * (n - r)!) * ((r + n - r + 1) / (r * (n - r + 1)))  := h₇
          _ = (n + 1)! / (r ! * (n + 1 - r)!)                                        := by egg [Nat.add_comm, Nat.add_sub_cancel, Nat.mul_comm, Nat.mul_assoc, Nat.div_mul_div_comm, Nat.factorial, Nat.mul_factorial_pred, todo; h₂, h₄, h₅, h₆]

/- Manual calculation:

calc (n + 1).choose r
  _ = n.choose (r - 1) + n.choose r                                          := proposition_1_14 ..
  _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)           := by rw [hi h₁, hi h₂, h₃]
  _ = (n !) / ((r - 1)! * (n - r)! * (n - r + 1)) + (n !) / (r ! * (n - r)!) := by egg [Nat.factorial, Nat.mul_assoc, Nat.mul_comm]
  _ = (n !) / ((r - 1)! * (n - r)!) * ((r + n - r + 1) / (r * (n - r + 1)))  := h₇
  _ = (n !) / ((r - 1)! * (n - r)!) * ((n + 1) / (r * (n - r + 1)))          := by egg [Nat.add_comm, Nat.add_sub_cancel]
  _ = (n ! * (n + 1)) / ((r - 1)! * (n - r)! * r * (n - r + 1))              := by simp [Nat.div_mul_div_comm h₄ h₅, Nat.mul_assoc]
  _ = (n + 1)! / (r ! * (n + 1 - r)!)                                        := ...
-/
