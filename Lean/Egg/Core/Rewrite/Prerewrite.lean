import Egg.Core.Directions
import Egg.Core.Congr
open Lean Meta

namespace Egg

-- Note: We don't create `Prerewrite`s directly, but use `Prerewrite.from?` instead.
structure Prerewrite extends Congr where private mk ::
  qvars : MVarIdSet
  proof : Expr
  deriving Inhabited

def Prerewrite.from? (proof type : Expr) (cfg : Config.Normalization) (normalize : Bool) :
    MetaM (Option Prerewrite) := do
  let type ← if normalize then Egg.normalize type cfg else pure type
  let (args, _, prop) ← withReducible do forallMetaTelescopeReducing type
  let proof := mkAppN proof args
  let qvars : MVarIdSet := args.foldl (·.insert ·.mvarId!) ∅
  if let some cgr ← Congr.from? prop then
    return some { cgr with proof, qvars }
  -- Note: We need this to reduce abbrevs which don't unfold to `∀ ...`, but rather just `_ ~ _`.
  else if let some cgr ← Congr.from? (← withReducible do reduce (skipTypes := false) prop) then
    return some { cgr with proof, qvars }
  else if (← inferType prop).isProp then
    let cgr : Congr := { rel := .eq, lhs := prop, rhs := .const ``True [] }
    let proof ← mkEqTrue proof
    return some { cgr with proof, qvars }
  else
    return none

def Prerewrite.forDir (pre : Prerewrite) : Direction → MetaM Prerewrite
  | .forward  => return pre
  | .backward => return { pre with
    lhs   := pre.rhs,
    rhs   := pre.lhs,
    proof := ← pre.rel.mkSymm pre.proof
  }
