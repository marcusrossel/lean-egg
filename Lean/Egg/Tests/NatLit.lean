import Egg

-- Tests involving conversions between `Nat.zero` and `Nat.succ _` and `.lit (.natVal _)`.

example : 0 = Nat.zero := by
  egg

example : 1 = Nat.succ 0 := by
  egg

example : Nat.succ 1 = Nat.succ (Nat.succ Nat.zero) := by
  egg

example : 1 + 2 = 3 := by
  egg [Nat.add]

example : Int.ofNat (Nat.succ 1) = Int.ofNat (Nat.succ (Nat.succ Nat.zero)) := by
  egg

example (h : ∀ n, Nat.succ n = n + 1) : 1 = Nat.zero + 1 := by
  egg [h]

elab "app" n:num fn:ident arg:term : term => open Lean.Elab.Term in do
  let fn ← elabTerm fn none
  let rec go (n : Nat) := if n = 0 then elabTerm arg none else return .app fn <| ← go (n - 1)
  go n.getNat

-- Note: If we go to `61`, egg can't handle it anymore.
example : (app 60 Nat.succ (nat_lit 0)) = (nat_lit 60) := by egg

-- Note: This produces a gigantic proof.
example (f : Nat → Nat) (h : ∀ x, f x = x.succ) : 30 = app 30 f 0 := by
  egg [h]

-- TODO: Add more tests involving rewrites with Nat.succ or Nat.zero.
