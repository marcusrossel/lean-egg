import Lean
import Std.Lean.Meta.DiscrTree
import Std.Lean.HashSet

open Lean
open Meta (DiscrTree)

namespace Egg

-- TODO: Can we effectively use a discr tree here?
structure TypeIndexT.State where
  typeIdxs    : ExprMap Nat := {}
  nextTypeIdx : Nat         := 0

abbrev TypeIndexT (m : Type → Type) := StateT TypeIndexT.State m

namespace TypeIndexT

-- Note: If the given type does not have an index yet it is assigned one.
--
-- Note: `HashMap.find?` relies on `BEq`, which for `Expr`s holds up to α-equivalence.
--
-- Note: This can be generalized by replacing `MetaM` with `[Monad m] [MonadLift MetaM m]`. But we
--       have no use for this generality at the moment.
def typeIdx (ty : Expr) : TypeIndexT MetaM Nat := do
  let s ← get
  match s.typeIdxs.find? ty with
  | some idx => return idx
  | none =>
    let idx := s.nextTypeIdx
    let idxs' := s.typeIdxs.insert ty idx
    set { s with nextTypeIdx := idx + 1, typeIdxs := idxs' }
    return idx

def withFreshIndex [Functor m] (t : TypeIndexT m α) : m α :=
  Prod.fst <$> t.run {}

def getTypes [Monad m] : TypeIndexT m (Array Expr) :=
  return (← get).typeIdxs.toArray.qsort (·.snd < ·.snd) |>.map (·.fst)
