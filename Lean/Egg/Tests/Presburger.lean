import Egg

@[egg presburg]
axiom free (x : Nat) : ¬(0 = x + 1)

@[egg presburg]
axiom succ_inj (x y : Nat) : x + 1 = y + 1 → x = y

@[egg presburg]
axiom add_zero (x : Nat) : x + 0 = x

@[egg presburg]
axiom add_succ (x y : Nat) : x + (y + 1) = (x + y) + 1

@[egg presburg]
axiom induct (P : Nat → Prop) : P 0 ∧ (∀ x, P x → P (x + 1)) → (∀ y, P y)

example : 0 ≠ 1 := by
  egg presburg

-- TODO: Are there any interesting theorems we can solve?
--       Most interesting theorems need induction.
