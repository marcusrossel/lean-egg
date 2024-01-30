import Egg

-- TODO: Would it be nicer to allow any number of terms to be supplied into the list of rewrites
--       and make all of them potential bases by adding them to the e-graph?

example (h : True) : True := by
  egg from h

example (h : 0 = 0) : 0 = 0 := by
  egg from h

example (a b : Nat) (h : a = b) : a = b := by
  egg [Nat.add_comm] from h

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₂] from h₁

-- TODO: Removing the last `p` in the goal causes 'maximum recursion depth has been reached'.
example (h : p ∧ q ∧ r) (assoc : ∀ a b c, (a ∧ b) ∧ c ↔ a ∧ (b ∧ c)) (idem : ∀ a, a ↔ a ∧ a) :
    r ∧ r ∧ q ∧ p ∧ q ∧ r ∧ p := by
  egg [And.comm, assoc, idem] from h

inductive P : Nat → Prop
example (hp : P Nat.zero.succ) (h : ∀ n, P n ↔ P n.succ) : P Nat.zero.succ.succ.succ.succ := by
  egg [h] from hp
