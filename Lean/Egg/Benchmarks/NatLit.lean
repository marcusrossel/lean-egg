import Egg

-- Tests involving conversions between `Nat.zero` and `Nat.succ _` and `.lit (.natVal _)`.

set_option egg.reporting true
set_option egg.flattenReports true

set_option egg.natLit true

elab "app" n:num fn:ident arg:term : term => open Lean.Elab.Term in do
  let fn ← elabTerm fn none
  let rec go (n : Nat) := if n = 0 then elabTerm arg none else return .app fn <| ← go (n - 1)
  go n.getNat

set_option egg.timeLimit 10 in
set_option egg.builtins false in
example : (app 70 Nat.succ (nat_lit 0)) = (nat_lit 70) := by egg

-- Note: This produces a gigantic proof.
example (f : Nat → Nat) (h : ∀ x, f x = x.succ) : 30 = app 30 f 0 := by
  egg [h]
