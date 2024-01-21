import Egg

set_option trace.egg true

-- While egg happily rewrites under binders, we can't reconstruct the proof using our current
-- technique. Below, the problem is that we're trying to rewrite from `λ x, x` to `λ x, x + 0` and
-- when we view the relevant subexpressions for the rewrite we get:
-- * lhs: `(fvar 123)`
-- * rhs: `(fvar 456) + 0`
-- That is, the bound variable `x` on the left and right side gets viewed as different fvars.
-- Thus, we can't unify the equality `(fvar 123) = (fvar 456) + 0` with the rewrite `?m = ?m + 0`.
-- A solution to this would be to make sure that when we view subexpressions which are contained in
-- λs, we replace the newly bound fvars on one side with those of the other side (e.g. by using
-- `Expr.replace` as in `Rewrite.fresh`).
example : (fun x : Nat => x) = (fun x => Nat.add x .zero) := by
  egg [(sorry : ∀ x : Nat, x = Nat.add x .zero)]

def f : Bool → Nat
  | false => 0
  | true => 1

-- TODO: The equational lemmas that are being produced aren't really useful.
--       Cf. the following post for better equations: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/getEqnsFor.3F.20non-recursive.20function
set_option trace.egg true in
example : f false = 0 := by
  egg [f]
