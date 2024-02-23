import Egg.Core.Rewrites.Directions
import Egg.Core.MVars
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg.Rewrite

structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof    : Expr
  src      : Source
  lhsMVars : MVars
  rhsMVars : MVars

-- Note: We normalize the `lhs` and `rhs` of the rewrite.
--
-- Note: It isn't sufficient to take the `args` as a rewrite's holes, as implicit arguments will
--       already be instantiated as mvars during type inference. For example, the type of
--       `theorem t : ∀ {x}, x + 0 = 0 + x := Nat.add_comm _ _` will be directly inferred as
--       `?x + 0 = 0 + ?x`.
--       On the other hand, we might be collecting too many mvars right now as a rewrite could
--       possibly contain mvars which weren't quantified (e.g. if it comes from the local context).
--
-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, cf.
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
def from? (proof : Expr) (type : Expr) (src : Source) : MetaM (Option Rewrite) := do
  let mut (args, _, type) ← forallMetaTelescope (← instantiateMVars type)
  type ← normalize type
  let proof := mkAppN proof args
  let some cgr ← Congr.from? type | return none
  let lhsMVars := MVars.collect cgr.lhs
  let rhsMVars := MVars.collect cgr.rhs
  return some { cgr with proof, src, lhsMVars, rhsMVars }

def validDirs (rw : Rewrite) : Directions :=
  let exprDirs := Directions.satisfyingSuperset rw.lhsMVars.expr rw.rhsMVars.expr
  let lvlDirs  := Directions.satisfyingSuperset rw.lhsMVars.lvl rw.rhsMVars.lvl
  exprDirs.meet lvlDirs

-- Returns the same rewrite but with its type and proof potentially flipped to match the given
-- direction.
def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with lhs := rw.rhs, rhs := rw.lhs, proof := ← rw.rel.mkSymm rw.proof }

def eqProof (rw : Rewrite) : MetaM Expr := do
  match rw.rel with
  | .eq  => return rw.proof
  | .iff => mkPropExt rw.proof

-- TODO: Factor out some parts of this as functions on `MVars`.
-- Returns the same rewrite but with all (expression and level) mvars replaced by fresh mvars. This
-- is used during proof reconstruction, as rewrites may be used multiple times but instantiated
-- differently. If we don't use fresh mvars, the mvars will already be assigned and new assignment
-- (via `isDefEq`) will fail.
def fresh (rw : Rewrite) (src : Source := rw.src) : MetaM Rewrite := do
  let (mvarSubst, lmvarSubst, lhsMVars) ← mkSubsts ∅ ∅ rw.lhsMVars
  let (mvarSubst, lmvarSubst, rhsMVars) ← mkSubsts mvarSubst lmvarSubst rw.rhsMVars
  let lhs   := applySubsts rw.lhs   mvarSubst lmvarSubst
  let rhs   := applySubsts rw.rhs   mvarSubst lmvarSubst
  let proof := applySubsts rw.proof mvarSubst lmvarSubst
  return { rw with lhs, rhs, proof, src, lhsMVars, rhsMVars }
where
  applySubsts (e : Expr) (mvarSubst : HashMap MVarId Expr) (lmvarSubst : HashMap LMVarId Level) : Expr :=
    let replaceLvl : Level → Option Level
      | .mvar id => lmvarSubst.find? id
      | _ => none
    let replaceExpr : Expr → Option Expr
      | .mvar id         => mvarSubst.find? id
      | .sort lvl        => Expr.sort <| lvl.replace replaceLvl
      | .const name lvls => Expr.const name <| lvls.map (·.replace replaceLvl)
      | _                => none
    e.replace replaceExpr

  mkSubsts (mvarSubst : HashMap MVarId Expr) (lmvarSubst : HashMap LMVarId Level) (mvars : MVars) :
      MetaM (HashMap MVarId Expr × HashMap LMVarId Level × MVars) := do
    let mut mvarSubst          := mvarSubst
    let mut lmvarSubst         := lmvarSubst
    let mut freshMVars : MVars := {}
    for var in mvars.expr do
      if let some fresh := mvarSubst.find? var then
        freshMVars := { freshMVars with expr := freshMVars.expr.insert fresh.mvarId! }
      else
        let fresh ← mkFreshExprMVar (← var.getType)
        mvarSubst := mvarSubst.insert var fresh
        freshMVars := { freshMVars with expr := freshMVars.expr.insert fresh.mvarId! }
    for var in mvars.lvl do
      if let some fresh := lmvarSubst.find? var then
        freshMVars := { freshMVars with lvl := freshMVars.lvl.insert fresh.mvarId! }
      else
        let fresh ← mkFreshLevelMVar
        lmvarSubst := lmvarSubst.insert var fresh
        freshMVars := { freshMVars with lvl := freshMVars.lvl.insert fresh.mvarId! }
    return (mvarSubst, lmvarSubst, freshMVars)

def instantiateMVars (rw : Rewrite) : MetaM Rewrite :=
  return { rw with
    lhs   := ← Lean.instantiateMVars rw.lhs
    rhs   := ← Lean.instantiateMVars rw.rhs
    proof := ← Lean.instantiateMVars rw.proof
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
