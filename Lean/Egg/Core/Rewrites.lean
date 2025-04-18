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

namespace Condition

inductive Kind where
  | proof
  | tcInst

def Kind.isProof : Kind → Bool
  | proof  => true
  | tcInst => false

def Kind.isTcInst : Kind → Bool
  | proof  => false
  | tcInst => true

def Kind.forType? (ty : Expr) : MetaM (Option Kind) := do
  -- Since type classes can also be propositions, we do the type class check first.
  if (← Meta.isClass? ty).isSome then
    return some .tcInst
  else if ← Meta.isProp ty then
    return some .proof
  else
    return none

structure _root_.Egg.Rewrite.Condition where
  kind  : Kind
  -- Without instantiation, this `expr` is an mvar. When instantiated, the condition is considered
  -- proven.
  expr  : Expr
  type  : Expr
  -- These are the mvars of `type`.
  mvars : MVars

-- Conditions can become proven during type class specialization. We still need to keep these
-- conditions in order to use their `expr` during proof reconstruction. Proven conditions are not
-- encoded and thus transparent to the backend.
def isProven (cond : Condition) : Bool :=
  !cond.expr.isMVar

nonrec def instantiateMVars (cond : Condition) : MetaM Condition := do
  return { cond with
    expr  := ← instantiateMVars cond.expr
    type  := ← instantiateMVars cond.type
    mvars := ← cond.mvars.removeAssigned
  }

end Condition

-- Note: We don't create `Rewrite`s directly, but use `Rewrite.from` instead.
structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof : Expr
  src   : Source
  conds : Array Condition
  mvars : Rewrite.MVars
  -- This is a means of fixing the set of directions for the rewrite manually.
  private dirs? : Option Directions
  deriving Inhabited

def from? (proof type : Expr) (src : Source) (cfg : Config.Normalization) (normalize := true) :
    MetaM (Option Rewrite) := do
  let type ← if normalize then Egg.normalize type cfg else pure type
  let mut (args, _, prop) ← withReducible do forallMetaTelescopeReducing type
  let mut proof := mkAppN proof args
  let cgr ←
    if let some cgr ← Congr.from? prop then
      pure cgr
    -- Note: We need this to reduce abbrevs which don't unfold to `∀ ...`, but rather just `_ ~ _`.
    else if let some cgr ← Congr.from? (← withReducible do reduce (skipTypes := false) prop) then
      pure cgr
    else if (← inferType prop).isProp then
      proof ← mkEqTrue proof
      pure { rel := .eq, lhs := prop, rhs := .const ``True [] }
    else
      return none
  let mLhs  ← MVars.collect cgr.lhs
  let mRhs  ← MVars.collect cgr.rhs
  let conds ← collectConds args mLhs mRhs
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs, dirs? := none }
where
  collectConds (args : Array Expr) (mLhs mRhs : MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    -- Because of type class instance erasure, we need to make sure that all required type class
    -- instances are synthesizable, so we add them as conditions to the rewrite. We only do this for
    -- type class instances though which are erased as part of a type class instance term, because
    -- "standalone" type class instances are represented by their erased term.
    -- For example, we wouldn't add `?i` as a condition in `@Inhabited.default α ?i` as the erasure
    -- of `?i` is precisely its type `Inhabited α`. In constrast, we would add `?j` as a condition
    -- in `@HAdd.hAdd α α α (@instHAdd α j?)`, as the type of the entire type class instance term is
    -- `HAdd α α α`, which doesn't match the type of `?j : Add α`.
    for tcInstMVar in mLhs.nestedTcInsts.union mRhs.nestedTcInsts do
      -- TODO: Collecting all this information seems a bit superfluos. Perhaps we should redefine
      --       `Condition` (or split it into two types) as we only consider propositions and type
      --       class instances anyway.
      conds := conds.push {
        kind  := .tcInst,
        expr  := .mvar tcInstMVar,
        type  := ← tcInstMVar.getType,
        mvars := ← MVars.collect (← tcInstMVar.getType)
      }
    -- Even when erasure is active, we still do not consider the mvars contained in erased terms to
    -- be conditions. Thus, we start by considering all mvars in the target as non-conditions and
    -- take their type mvar closure. This closure will necessarily contain the mvars contained in
    -- the types of erased terms, which therefore don't need to be added separately (as in,
    -- contingent upon the erasure configuration).
    let inTarget : MVarIdSet := mLhs.inTarget.union mRhs.inTarget
    let mut noCond ← inTarget.typeMVarClosure
    for arg in args.reverse do
      if noCond.contains arg.mvarId! then continue
      -- As we encode conditions as part of a rewrite's searcher its mvars also become
      -- non-conditions. That's why we traverse the list of arguments above in reverse.
      noCond := noCond.union (← MVarIdSet.typeMVarClosure {arg.mvarId!})
      let ty ← arg.mvarId!.getType
      let mvars ← MVars.collect ty
      let some kind ← Condition.Kind.forType? ty
        | throwError m!"Rewrite {src} requires condition of type '{ty}' which is neither a proof nor an instance."
      conds := conds.push { kind, expr := arg, type := ty, mvars }
    return conds

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
  return some { cgr with proof, src, conds := #[], mvars.lhs := {}, mvars.rhs := {}, dirs? := none }

-- If `disallowLoneMVar` is set, we prune directions where the pattern is just an mvar.
def fixDirs (rw : Rewrite) (dirs : Directions) (disallowLoneMVar := false) : Rewrite := Id.run do
  let mut d := dirs
  if disallowLoneMVar then
    if rw.lhs.isMVar then d := d.without .forward
    if rw.rhs.isMVar then d := d.without .backward
  { rw with dirs? := d }

def validDirs (rw : Rewrite) (conditionSubgoals : Bool) : Directions := Id.run do
  if let some fixed := rw.dirs? then return fixed
  let mut visibleExprLhs  := rw.mvars.lhs.visibleExpr
  let mut visibleExprRhs  := rw.mvars.rhs.visibleExpr
  let mut visibleLevelLhs := rw.mvars.lhs.visibleLevel
  let mut visibleLevelRhs := rw.mvars.rhs.visibleLevel
  if !conditionSubgoals then
    -- MVars appearing in propositional conditions are going to be part of the rewrite's LHS, so
    -- they can (and should be) ignored when computing valid directions.
    -- TODO: How does visibility work in conditions?
    let propCondExpr  : MVarIdSet  := rw.conds.filter (·.kind.isProof) |>.foldl (init := ∅) (·.union ·.mvars.visibleExpr)
    let propCondLevel : LMVarIdSet := rw.conds.filter (·.kind.isProof) |>.foldl (init := ∅) (·.union ·.mvars.visibleLevel)
    visibleExprLhs  := visibleExprLhs.filter  (!propCondExpr.contains ·)
    visibleExprRhs  := visibleExprRhs.filter  (!propCondExpr.contains ·)
    visibleLevelLhs := visibleLevelLhs.filter (!propCondLevel.contains ·)
    visibleLevelRhs := visibleLevelRhs.filter (!propCondLevel.contains ·)
  let exprDirs := Directions.satisfyingSuperset visibleExprLhs visibleExprRhs
  let lvlDirs  := Directions.satisfyingSuperset visibleLevelLhs visibleLevelRhs
  let mut dirs := exprDirs.meet lvlDirs
  -- To avoid rewrites of the form "?m => ...", we disallow directions where the pattern is just an
  -- mvar.
  if rw.lhs.isMVar then dirs := dirs.without .forward
  if rw.rhs.isMVar then dirs := dirs.without .backward
  return dirs

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
    proof     := ← Lean.instantiateMVars rw.proof
    mvars.lhs := ← rw.mvars.lhs.removeAssigned
    mvars.rhs := ← rw.mvars.rhs.removeAssigned
    conds     := ← rw.conds.mapM (·.instantiateMVars)
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

-- TODO: This is unnecessarilly inefficient during proof reconstruction. At some point we may want
--       to redefine `Rewrites` using a better suited data structure like `HashMap Source Rewrite`.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? (·.src == src) rws
