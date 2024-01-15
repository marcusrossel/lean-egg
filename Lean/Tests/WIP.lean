import Egg

set_option trace.egg true

-- We seem to just rewrite under binders:
-- This can cause invalid capture of bvars, but sofar I haven't seen any proofs of invalid results
-- from this.
example : (fun x : Nat => x) = (fun x => Nat.add x .zero) := by
  egg [(sorry : ∀ x : Nat, x = Nat.add x .zero)]

-- TODO: How should we handle rewrites like `h`? Such a statement basically amounts to stating that
--       `Unit` is a subsingleton, which is a sensible statement.
--       We could introduce special handling for such statements by detecting them, trying to prove
--       that the given type is a singleton type and in that case adding the theorem
--       `∀ x, x = default` instead.
example (a b : Unit) (h : ∀ x y : Unit, x = y) : a = b := by
  egg [h]

def f : Bool → Nat
  | false => 0
  | true => 1

-- TODO: The equational lemmas that are being produced aren't really useful.
--       Cf. the following post for better equations: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/getEqnsFor.3F.20non-recursive.20function
set_option trace.egg true in
example : f false = 0 := by
  egg [f]
