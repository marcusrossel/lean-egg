import Lean
open Lean

namespace Egg

-- TODO: Can we effectively use a discr tree for `types`?
structure IndexT.State where
  types       : ExprMap Nat := {}
  nextTypeIdx : Nat         := 0

abbrev IndexT := StateT IndexT.State

namespace IndexT

instance [MonadLift m₁ m₂] : MonadLift (IndexT m₁) (IndexT m₂) where
  monadLift a := (a.run ·)

-- Note: The functions below using `MetaM` can be generalized with `[Monad m] [MonadLift MetaM m]`.
--       But we have no use for this generality at the moment.

-- Note: If the given type does not have an index yet it is assigned one.
--
-- Note: `HashMap.find?` relies on `BEq`, which for `Expr`s holds up to α-equivalence.
def typeIdx (ty : Expr) : IndexT MetaM Nat := do
  let s ← get
  match s.types.find? ty with
  | some idx => return idx
  | none =>
    let idx := s.nextTypeIdx
    let types' := s.types.insert ty idx
    set { s with nextTypeIdx := idx + 1, types := types' }
    return idx

def getTypes : IndexT MetaM (Array Expr) :=
  return (← get).types.toArray.qsort (·.snd < ·.snd) |>.map (·.fst)

def withFreshIndex [Functor m] (t : IndexT m α) : m α :=
  Prod.fst <$> t.run {}
