import Egg

-- Tests involving conversions between `Nat.zero` and `Nat.succ _` and `.lit (.natVal _)`.

set_option egg.natLit true

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

example : 1 = Nat.zero + 1 := by
  egg [Nat.succ_eq_add_one]

elab "app" n:num fn:ident arg:term : term => open Lean.Elab.Term in do
  let fn ← elabTerm fn none
  let rec go (n : Nat) := if n = 0 then elabTerm arg none else return .app fn <| ← go (n - 1)
  go n.getNat

example : (app 100 Nat.succ (nat_lit 0)) = (nat_lit 100) := by egg

-- Note: This produces a gigantic proof.
example (f : Nat → Nat) (h : ∀ x, f x = x.succ) : 30 = app 30 f 0 := by
  egg [h]

example : 12345 + 67890 = 80235 := by
  egg

example : 12345 - 67890 = 0 := by
  egg

example : 67890 - 12345 = 55545 := by
  egg

example : 12345 * 67890 = 838102050 := by
  egg

example : 1234 ^ 5 = 2861381721051424 := by
  egg

example : 12345 / 67890 = 0 := by
  egg

example : 67890 / 12345 = 5 := by
  egg

example : 12345 / 0 = 0 := by
  egg

example : 67890 % 12345 = 6165 := by
  egg

example : 12345 % 67890 = 12345 := by
  egg

example : 12345 % 0 = 12345 := by
  egg

set_option egg.natLit false in
set_option egg.natReduceRws false in
/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : ∀ f : Nat → Nat, f (1 + 1) = x) : id 2 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (1 + 1) = x) : id 2 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (3 - 2) = x) : id 1 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (2 * 3) = x) : id 6 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (4 / 2) = x) : id 2 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (5 % 3) = x) : id 2 = x := by
  egg [h]

example (h : ∀ f : Nat → Nat, f (2 ^ 3) = x) : id 8 = x := by
  egg [h]
