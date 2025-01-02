import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Collect
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg.Rewrite

protected structure MVars where
  lhs : MVars
  rhs : MVars
  deriving Inhabited

structure Condition where
  -- Without instantiation, this `expr` is an mvar. When instantiated, the condition is considered
  -- proven.
  expr  : Expr
  type  : Expr
  -- These are the mvars of `type`.
  mvars : MVars

-- Conditions can become proven during type class specialization. We still need to keep these
-- conditions in order to use their `expr` during proof reconstruction. Proven conditions are not
-- encoded and thus transparent to the backend.
def Condition.isProven (cond : Condition) : Bool :=
  !cond.expr.isMVar

nonrec def Condition.instantiateMVars (cond : Condition) : MetaM Condition := do
  return { cond with
    expr  := ← instantiateMVars cond.expr
    type  := ← instantiateMVars cond.type
    mvars := ← cond.mvars.removeAssigned
  }

-- Note: We don't create `Rewrite`s directly, but use `Rewrite.from` instead.
structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof : Expr
  src   : Source
  conds : Array Condition
  mvars : Rewrite.MVars
  deriving Inhabited

structure Config extends Config.Normalization, Config.Erasure where
  amb : MVars.Ambient

instance : Coe Config Config.Normalization where
  coe := Config.toNormalization

instance : Coe Config Config.Erasure where
  coe := Config.toErasure

partial def from? (proof type : Expr) (src : Source) (cfg : Config) (normalize := true) :
    MetaM (Option Rewrite) := do
  let type ← if normalize then Egg.normalize type cfg else pure type
  let mut (args, _, eqOrIff?) ← forallMetaTelescopeReducing type
  let cgr ←
    if let some cgr ← Congr.from? eqOrIff? then
      pure cgr
    else if let some cgr ← Congr.from? (← reduce (skipTypes := false) eqOrIff?) then
      pure cgr
    else
      return none
  let proof := mkAppN proof args
  let mLhs  ← MVars.collect cgr.lhs cfg.amb
  let mRhs  ← MVars.collect cgr.rhs cfg.amb
  let conds ← collectConds args mLhs mRhs
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs }
where
  collectConds (args : Array Expr) (mLhs mRhs : MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    -- Even when erasure is active, we still do not consider the mvars contained in erased terms to
    -- be conditions. Thus, we start by considering all mvars in the target as non-conditions and
    -- take their type mvar closure. This closure will necessarily contain the mvars contained in
    -- the types of erased terms, which therefore don't need to be added separately (as in,
    -- contingent upon the erasure configuration).
    let inTarget : MVarIdSet := mLhs.inTarget.union mRhs.inTarget
    let mut noCond ← inTarget.typeMVarClosure (ignore := cfg.amb.expr)
    for arg in args do
      if noCond.contains arg.mvarId! then continue
      let ty ← arg.mvarId!.getType
      let mvars ← MVars.collect ty cfg.amb
      conds := conds.push { expr := arg, type := ty, mvars }
    return conds

def isConditional (rw : Rewrite) : Bool :=
  !rw.conds.isEmpty

def validDirs (rw : Rewrite) (cfg : Config.Erasure) : Directions :=
  let exprDirs := Directions.satisfyingSuperset (rw.mvars.lhs.visibleExpr cfg) (rw.mvars.rhs.visibleExpr cfg)
  let lvlDirs  := Directions.satisfyingSuperset (rw.mvars.lhs.visibleLevel cfg) (rw.mvars.rhs.visibleLevel cfg)
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

def freshWithSubst (rw : Rewrite) (src : Source := rw.src) : MetaM (Rewrite × MVars.Subst) := do
  let (mLhs, subst)  ← rw.mvars.lhs.fresh
  let (mRhs, subst)  ← rw.mvars.rhs.fresh (init := subst)
  let (conds, subst) ← freshConds (init := subst)
  -- Note: The `conds` already have `subst` applied. So If you have more substitution targets in the
  --       future, you might need to consider that.
  let rw' := { rw with
    src
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    conds := conds
    mvars := { lhs := mLhs, rhs := mRhs }
  }
  return (rw', subst)
where
  freshConds (init : MVars.Subst) : MetaM (Array Condition × MVars.Subst) := do
    let mut subst := init
    let mut conds := #[]
    for cond in rw.conds do
      let (_, s) ← (← MVars.collect cond.expr ∅).fresh (init := subst)
      let (mvars, s) ← cond.mvars.fresh (init := s)
      conds := conds.push { expr := s.apply cond.expr, type := s.apply cond.type, mvars }
      subst := s
    return (conds, subst)

-- Returns the same rewrite but with all (expression and level) mvars replaced by fresh mvars. This
-- is used during proof reconstruction, as rewrites may be used multiple times but instantiated
-- differently. If we don't use fresh mvars, the mvars will already be assigned and new assignment
-- (via `isDefEq`) will fail.
def fresh (rw : Rewrite) (src : Source := rw.src) : MetaM Rewrite :=
  Prod.fst <$> rw.freshWithSubst src

def instantiateMVars (rw : Rewrite) : MetaM Rewrite :=
  return { rw with
    lhs       := ← Lean.instantiateMVars rw.lhs
    rhs       := ← Lean.instantiateMVars rw.rhs
    proof     := ← Lean.instantiateMVars rw.proof
    mvars.lhs := ← rw.mvars.lhs.removeAssigned
    mvars.rhs := ← rw.mvars.rhs.removeAssigned
    conds     := ← rw.conds.mapM (·.instantiateMVars)
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction. At some point we may want
--       to redefine `Rewrites` using a better suited data structure like `HashMap Source Rewrite`.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? (·.src == src) rws
