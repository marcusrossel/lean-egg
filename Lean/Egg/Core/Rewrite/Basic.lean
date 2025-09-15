import Egg.Core.Rewrite.Prerewrite
import Egg.Core.Rewrite.Condition
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Collect
import Egg.Core.Source
open Lean Meta Std

namespace Egg

structure Rewrite.Conditions where
  active          : Array Rewrite.Condition
  synthesized     : MVarIdSet
  unsynthesizable : MVarIdSet
deriving Inhabited

instance : EmptyCollection Rewrite.Conditions where
  emptyCollection := { active := #[], synthesized := ∅, unsynthesizable := ∅ }

-- Note: We don't create `Rewrite`s directly, but use `Rewrite.from?` instead.
structure Rewrite extends Prerewrite where private mk ::
  conds : Rewrite.Conditions
  mvars : Rewrite.MVars
deriving Inhabited

-- Note: It suffices to iterate over the qvars and the body mvars, as any mvars not appearing in
--       either of these must be the *type* of some mvar which does appear. But types can never turn
--       into conditions, so we don't need to consider them.
private def collectConditions (qvars : MVarIdSet) (mLhs mRhs : MVars) : MetaM Rewrite.Conditions := do
  let mut mvars := qvars
  mvars := mLhs.expr.fold (init := mvars) fun acc m _ => acc.insert m
  mvars := mRhs.expr.fold (init := mvars) fun acc m _ => acc.insert m
  let mut active := #[]
  let mut synthesized := ∅
  let mut unsynthesizable := ∅
  for mvar in mvars do
    match ← Rewrite.Condition.from? mvar mLhs with
    | .none            => continue
    | .synthesized     => synthesized     := synthesized.insert mvar
    | .unsynthesizable => unsynthesizable := unsynthesizable.insert mvar
    | .some cond       => active          := active.push cond
  return { active, synthesized, unsynthesizable }

def Prerewrite.complete (pre : Prerewrite) (dir : Direction) : MetaM Rewrite := do
  let pre  ← pre.forDir dir
  let mLhs ← MVars.collect pre.lhs
  let mRhs ← MVars.collect pre.rhs
  let conds ← collectConditions pre.qvars mLhs mRhs
  return { pre with conds, mvars := ⟨mLhs, mRhs⟩ }

namespace Rewrite

def from? (dir : Direction) (proof type : Expr) (cfg : Config.Normalization) (normalize := true) :
    MetaM (Option Rewrite) := do
  let some pre ← Prerewrite.from? proof type cfg normalize | return none
  pre.complete dir

def both? (proof type : Expr) (cfg : Config.Normalization) (normalize := true) :
    MetaM <| Option (Rewrite × Rewrite) := do
  let some pre ← Prerewrite.from? proof type cfg normalize | return none
  -- We are sharing mvars here. That should be ok, as we always create fresh mvars when *using* a
  -- rewrite anyway.
  return some (← pre.complete .forward, ← pre.complete .backward)

-- Returns `none` if the given type is already ground.
def ground? (proof type : Expr) (cfg : Config.Normalization) (normalize := true) :
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
  return some { cgr with qvars := ∅, proof, conds := ∅, mvars := ⟨{}, {}⟩ }

-- TODO: Do we need something like `covering` for levels?
inductive Violation where
  | rhsMVarInclusion (missing : MVarIdSet)
  | rhsUVarInclusion (missing : LMVarIdSet)
  | lhsSingleMVar    (mvar : MVarId)
  | mVarCovering     (missing : MVarIdSet)
  | tcMVarInclusion  (missing : MVarIdSet)
  | tcUVarInclusion  (missing : LMVarIdSet)
  | unsynthesizable  (conds : MVarIdSet)

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
def violations (rw : Rewrite) (subgoals : Bool) : MetaM (List Violation) := do
  let mut violations : List Violation := []
  -- Checks that there are no unsynthesizable conditions.
  unless rw.conds.unsynthesizable.isEmpty do
    violations := (.unsynthesizable rw.conds.unsynthesizable) :: violations
  -- Checks for `lhsSingleMVar`.
  let containsNonMVarProofConditions ← (return !subgoals) <&&> rw.conds.active.anyM fun cond =>
    (return cond.kind.isProof) <&&> cond.type.isNonAmbientMVar
  if ← rw.lhs.isNonAmbientMVar <&&> (return !containsNonMVarProofConditions) then
    violations := (.lhsSingleMVar rw.lhs.mvarId!) :: violations
  -- Checks for `rhsMVarInclusion`.
  let mut visible := rw.mvars.lhs.visibleExpr
  unless subgoals do visible := visible.merge (← condVisible .proof)
  let missing := rw.mvars.rhs.visibleExpr.eraseMany visible
  unless missing.isEmpty do violations := (.rhsMVarInclusion missing) :: violations
  -- Checks for `rhsUVarInclusion`.
  let mut visibleLvls := rw.mvars.lhs.visibleLevel
  unless subgoals do visibleLvls := visibleLvls.merge (← condVisibleLvls .proof)
  let missing := rw.mvars.rhs.visibleLevel.eraseMany visibleLvls
  unless missing.isEmpty do violations := (.rhsUVarInclusion missing) :: violations
  -- Checks for `tcMVarInclusion`.
  let missing := (← condVisible .tcInst).eraseMany visible
  unless missing.isEmpty do violations := (.tcMVarInclusion missing) :: violations
  -- Checks for `tcUVarInclusion`.
  let missing := (← condVisibleLvls .tcInst).eraseMany visibleLvls
  unless missing.isEmpty do violations := (.tcUVarInclusion missing) :: violations
  -- Checks for `mVarCovering`.
  let mut cov ← rw.qvars.filterM fun m => Meta.isTCInstance (.mvar m) <||> Meta.isProof (.mvar m)
  cov ← MVarIdSet.typeMVarClosure (cov.merge visible)
  let missing := rw.qvars.eraseMany cov
  unless missing.isEmpty do violations := (.mVarCovering missing) :: violations
  return violations
where
  condVisible (kind : Condition.Kind) : MetaM MVarIdSet := do
    let mut vis := ∅
    for cond in rw.conds.active do
      if cond.kind == kind then
        let mvars ← MVars.collect cond.type
        vis := vis.merge mvars.visibleExpr
    return vis
  condVisibleLvls (kind : Condition.Kind) : MetaM LMVarIdSet := do
    let mut vis := ∅
    for cond in rw.conds.active do
      if cond.kind == kind then
        let mvars ← MVars.collect cond.type
        vis := vis.merge mvars.visibleLevel
    return vis

def isValid (rw : Rewrite) (subgoals : Bool) : MetaM Bool :=
  return (← rw.violations subgoals).isEmpty

def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with
      lhs := rw.rhs, rhs := rw.lhs,
      proof := ← rw.rel.mkSymm rw.proof,
      mvars := { lhs := rw.mvars.rhs, rhs := rw.mvars.lhs }
    }

def eqProof (rw : Rewrite) : MetaM Expr := do
  match rw.rel with
  | .eq  => return rw.proof
  | .iff => mkPropExt rw.proof

def freshWithSubst (rw : Rewrite) : MetaM (Rewrite × MVars.Subst) := do
  let (qvars, subst) ← freshQVars
  let (mLhs, subst)  ← rw.mvars.lhs.fresh (init := subst)
  let (mRhs, subst)  ← rw.mvars.rhs.fresh (init := subst)
  let (conds, subst) ← freshConds (init := subst)
  let rw' := { rw with
    qvars, conds
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    mvars := { lhs := mLhs, rhs := mRhs }
  }
  return (rw', subst)
where
  freshQVars : MetaM (MVarIdSet × MVars.Subst) := do
    let mut subst : HashMap MVarId MVarId := ∅
    let mut fresh : MVarIdSet := ∅
    for qvar in rw.qvars do
      let m := (← mkFreshExprMVar none).mvarId!
      fresh := fresh.insert m
      subst := subst.insert qvar m
    return (fresh, { expr := subst, lvl := ∅ })
  freshConds (init : MVars.Subst) : MetaM (Conditions × MVars.Subst) := do
    let mut subst := init
    let mut active := #[]
    -- Note: Synthesized and unsynthesizable conditions can't have mvars, so we don't refresh them.
    for cond in rw.conds.active do
      let (fresh, s) ← cond.fresh subst
      active := active.push fresh
      subst := s
    return ({ rw.conds with active }, subst)

-- Returns the same rewrite but with all (expression and level) mvars replaced by fresh mvars. This
-- is used during proof reconstruction, as rewrites may be used multiple times but instantiated
-- differently. If we don't use fresh mvars, the mvars will already be assigned and new assignment
-- (via `isDefEq`) will fail.
def fresh (rw : Rewrite) : MetaM Rewrite :=
  Prod.fst <$> rw.freshWithSubst

-- Note: We have to compute `qvars`, `mLhs`, and `mRhs` in two steps, because we first need to prune
--       assign mvars, then recompute the set of conditions which might synthesize some instances,
--       and only then prune the newly synthesized instance mvars.
nonrec def instantiateMVars (rw : Rewrite) : MetaM Rewrite := do
  let mut qvars ← rw.qvars.filterM fun m => return !(← m.isAssigned)
  let mut mLhs  ← rw.mvars.lhs.removeAssigned
  let mut mRhs  ← rw.mvars.rhs.removeAssigned
  let conds ← collectConditions qvars mLhs mRhs
  for s in conds.synthesized.merge conds.unsynthesizable do
    qvars := qvars.erase s
    mLhs  := { mLhs with expr := mLhs.expr.erase s }
    mRhs  := { mLhs with expr := mRhs.expr.erase s }
  return { rw with
    qvars, conds
    lhs   := ← instantiateMVars rw.lhs
    rhs   := ← instantiateMVars rw.rhs
    proof := ← instantiateMVars rw.proof
    mvars := ⟨mLhs, mRhs⟩
  }

end Rewrite
