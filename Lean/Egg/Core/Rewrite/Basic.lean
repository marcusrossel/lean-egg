import Egg.Core.Rewrite.Prerewrite
import Egg.Core.Rewrite.Condition
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Collect
import Egg.Core.Source
open Lean Meta

namespace Egg

-- Note: We don't create `Rewrite`s directly, but use `Rewrite.from?` instead.
structure Rewrite extends Prerewrite where private mk ::
  conds : Array Rewrite.Condition
  mvars : Rewrite.MVars
  src   : Source
  dir   : Direction
  deriving Inhabited

def Prerewrite.complete (pre : Prerewrite) (src : Source) (dir : Direction) : MetaM Rewrite := do
  let pre ← pre.forDir dir
  let mLhs  ← MVars.collect pre.lhs
  let mRhs  ← MVars.collect pre.rhs
  let conds ← collectConds pre.qvars mLhs mRhs
  return { pre with conds, mvars := ⟨mLhs, mRhs⟩, src, dir }
where
  -- Note: It suffices to iterate over the qvars and the body mvars, as any mvars not appearing in
  --       either of these must be the *type* of some mvar which does appear. But types can never
  --       turn into conditions, so we don't need to consider them.
  collectConds (qvars : MVarIdSet) (mLhs mRhs : MVars) : MetaM (Array Rewrite.Condition) := do
    let mut mvars := qvars
    mvars := mLhs.expr.fold (init := mvars) fun acc m _ => acc.insert m
    mvars := mRhs.expr.fold (init := mvars) fun acc m _ => acc.insert m
    mvars.toArray.filterMapM (Rewrite.Condition.from? · mLhs)

namespace Rewrite

def from?
    (dir : Direction) (proof type : Expr) (src : Source) (cfg : Config.Normalization)
    (normalize := true) : MetaM <| Option Rewrite := do
  let some pre ← Prerewrite.from? proof type cfg normalize | return none
  pre.complete src dir

-- Returns `none` if the given type is already ground.
def mkGroundEq? (proof type : Expr) (src : Source) (cfg : Config.Normalization) (normalize := true) :
    MetaM (Option Rewrite) := do
  unless (← inferType type).isProp do return none
  let type ← if normalize then Egg.normalize type cfg else pure type
  -- Aborts if the type is already ground.
  unless (← withReducible do whnf type).isForall do return none
  -- If level mvars are present we abort.
  if type.hasLevelMVar then return none
  let cgr : Congr := { rel := .eq, lhs := type, rhs := .const ``True [] }
  let proof ← mkEqTrue proof
  -- One direction suffices.
  return some { cgr with qvars := ∅, proof, conds := #[], mvars := ⟨{}, {}⟩, src, dir := .forward }

inductive Violation where
  | rhsMVarInclusion (missing : MVarIdSet)
  | lhsSingleMVar
  | covering (missing : MVarIdSet)
  | tcMVarInclusion

-- Note: To check `covering`, it suffices to check all qvars. The reason being that all vars are
--       either in the theorem body, the qvars, or the types of the former. The variables in the
--       body are covered by the LHS, as those in the RHS have to be a subset of that. The variables
--       appearing only in types are covered by their "children", by type inference. Thus, we only
--       have to check the qvars.
--
-- Note: In our procedure for checking `covering` we also assume that the construction for
--       conditions is correct. As a result, all proof and type class instance variables are
--       covered.
--
-- Note: When constructing `cov`, it's important to take the type mvar closure not only over
--       `visible`, as this does not suffice when `subgoals = true`.
--       Also note that taking the type mvar closure over the type class instances is ok, as we have
--       `tcMVarInclusion` anyway.
--
-- TODO: Handle levels.
def violation? (rw : Rewrite) (subgoals : Bool) : MetaM (Option Violation) := do
  -- Checks for `lhsSingleMVar`.
  if ← rw.lhs.isAmbientMVar <&&> ((return subgoals) <||> rw.conds.allM (·.type.isAmbientMVar)) then
    return some .lhsSingleMVar
  -- Checks for `rhsMVarInclusion`.
  let visible :=
    if subgoals then
      rw.mvars.lhs.visibleExpr
    else
      rw.conds.foldl (init := rw.mvars.lhs.visibleExpr) fun vis cond =>
        if cond.kind.isProof then vis.union cond.mvars.visibleExpr else vis
  let missing := rw.mvars.rhs.visibleExpr.subtract visible
  unless missing.isEmpty do return some (.rhsMVarInclusion missing)
  -- Checks for `tcMVarInclusion`.
  let tcVisible : MVarIdSet := rw.conds.foldl (init := ∅) fun vis cond =>
    if cond.kind.isTcInst then vis.union cond.mvars.visibleExpr else vis
  unless tcVisible.subset visible do return some .tcMVarInclusion
  -- Checks for `covering`.
  let mut cov ← rw.qvars.filterM fun m => Meta.isTCInstance (.mvar m) <||> Meta.isProof (.mvar m)
  cov ← MVarIdSet.typeMVarClosure (cov.union visible)
  let missing := rw.qvars.subtract cov
  unless missing.isEmpty do return some (.covering missing)
  return none

def isValid (rw : Rewrite) (subgoals : Bool) : MetaM Bool :=
  return (← rw.violation? subgoals).isNone

-- TODO: Flip the mvars and dir as well.
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
  -- TODO: Refresh the qvars.
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
      let (_, s) ← (← MVars.collect cond.expr).fresh (init := subst)
      let (mvars, s) ← cond.mvars.fresh (init := s)
      conds := conds.push {
        kind := cond.kind,
        expr := s.apply cond.expr,
        type := s.apply cond.type,
        mvars
      }
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
    qvars     := ← rw.qvars.filterM fun m => return !(← m.isAssigned)
    proof     := ← Lean.instantiateMVars rw.proof
    conds     := ← rw.conds.mapM (·.instantiateMVars)
    mvars.lhs := ← rw.mvars.lhs.removeAssigned
    mvars.rhs := ← rw.mvars.rhs.removeAssigned
  }

def pruneSynthesizableConditions (rw : Rewrite) : MetaM Rewrite := do
  let mut conds := #[]
  for cond in rw.conds do
    if cond.type.hasMVar then
      conds := conds.push cond
    else if (← Meta.synthInstance? cond.type).isNone then
      conds := conds.push cond
  return { rw with conds }

def eraseConditions (rw : Rewrite) : Rewrite :=
  { rw with conds := #[] }

def tcConditionMVars (rw : Rewrite) : MVarIdSet :=
  rw.conds.foldl (init := ∅) fun cs c =>
    if c.kind.isTcInst && !c.isProven then cs.insert c.expr.mvarId! else cs

end Rewrite

abbrev Rewrites := Array Rewrite

namespace Rewrites

-- Note: We are sharing mvars here. That should be ok, as we always create fresh mvars when *using*
--       a rewrite anyway.
def from? (proof type : Expr) (src : Source) (cfg : Config.Normalization) (normalize := true) :
    MetaM <| Option Rewrites := do
  let some pre ← Prerewrite.from? proof type cfg normalize | return none
  return #[← pre.complete src .forward, ← pre.complete src .backward]

-- TODO: This is unnecessarilly inefficient during proof reconstruction. At some point we may want
--       to redefine `Rewrites` using a better suited data structure like `HashMap Source Rewrite`.
def find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? (·.src == src) rws
