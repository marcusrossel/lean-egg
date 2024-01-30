import Egg

example (h : True) : True := by
  egg from h

example (h : 0 = 0) : 0 = 0 := by
  egg from h

example (a b : Nat) (h : a = b) : a = b := by
  egg [Nat.add_comm] from h

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₂] from h₁

inductive P : Nat → Prop
example (hp : P Nat.zero.succ) (h : ∀ n, P n ↔ P n.succ) : P Nat.zero.succ.succ.succ.succ := by
  egg [h] from hp
