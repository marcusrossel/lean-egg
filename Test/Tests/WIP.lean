import Egg

set_option trace.egg true

-- TODO: The equational lemmas that are being produced aren't really useful.
--       Cf. the following post for better equations: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/getEqnsFor.3F.20non-recursive.20function

def f : Bool → Nat
  | false => 0
  | true => 1

example : f false = 0 := by
  egg [f]
