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

def Kind.forType? (ty : Expr) : MetaM (Option Kind) := do
  if ← Meta.isProp ty then
    return some .proof
  else if (← Meta.isClass? ty).isSome then
    return some .tcInst
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
  deriving Inhabited

structure Config extends Config.Normalization, Config.Erasure where
  amb : MVars.Ambient

instance : Coe Config Config.Normalization where
  coe := Config.toNormalization

instance : Coe Config Config.Erasure where
  coe := Config.toErasure

def from? (proof type : Expr) (src : Source) (cfg : Config) (normalize := true) :
    MetaM (Option Rewrite) := do
  let type ← if normalize then Egg.normalize type cfg else pure type
  let mut (args, _, prop) ← withReducible do forallMetaTelescopeReducing type
  let mut proof := mkAppN proof args
  let cgr ←
    if let some cgr ← Congr.from? prop then
      pure cgr
    else if let some cgr ← Congr.from? (← withReducible do reduce (skipTypes := false) prop) then
      pure cgr
    else if (← inferType prop).isProp then
      proof ← mkEqTrue proof
      pure { rel := .eq, lhs := prop, rhs := .const ``True [] }
    else
      return none
  let mLhs  ← MVars.collect cgr.lhs cfg.amb
  let mRhs  ← MVars.collect cgr.rhs cfg.amb
  let conds ← collectConds args mLhs mRhs
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs }
where
  collectConds (args : Array Expr) (mLhs mRhs : MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    -- When type class instance erasure is active, we still need to make sure that all required type
    -- class instances are synthesizable, so we add them as conditions to the rewrite.
    if cfg.eraseTCInstances then
      for tcInstMVar in mLhs.tcInsts.union mRhs.tcInsts do
        -- TODO: Collecting all this information seems a bit superfluos. Perhaps we should redefine
        --       `Condition` (or split it into two types) as we only consider propositions and type
        --       class instances anyway.
        conds := conds.push {
          kind  := .tcInst,
          expr  := .mvar tcInstMVar,
          type  := ← tcInstMVar.getType,
          mvars := ← MVars.collect (← tcInstMVar.getType) cfg.amb
        }
    -- Even when erasure is active, we still do not consider the mvars contained in erased terms to
    -- be conditions. Thus, we start by considering all mvars in the target as non-conditions and
    -- take their type mvar closure. This closure will necessarily contain the mvars contained in
    -- the types of erased terms, which therefore don't need to be added separately (as in,
    -- contingent upon the erasure configuration).
    let inTarget : MVarIdSet := mLhs.inTarget.union mRhs.inTarget
    let mut noCond ← inTarget.typeMVarClosure (ignore := cfg.amb.expr)
    for arg in args.reverse do
      if noCond.contains arg.mvarId! then continue
      -- As we encode conditions as part of a rewrite's searcher its mvars also become
      -- non-conditions. That's why we traverse the list of arguments above in reverse.
      noCond := noCond.union (← MVarIdSet.typeMVarClosure {arg.mvarId!} (ignore := cfg.amb.expr))
      let ty ← arg.mvarId!.getType
      let mvars ← MVars.collect ty cfg.amb
      let some kind ← Condition.Kind.forType? ty
        | throwError m!"Rewrite {src} requires condition of type '{ty}' which is neither a proof nor an instance."
      conds := conds.push { kind, expr := arg, type := ty, mvars }
    return conds

-- Returns `none` if the given type is already ground.
def mkGroundEq? (proof type : Expr) (src : Source) (cfg : Config) (normalize := true) :
    MetaM (Option Rewrite) := do
  unless (← inferType type).isProp do return none
  let type ← if normalize then Egg.normalize type cfg else pure type
  -- Aborts if the type is already ground.
  unless (← withReducible do whnf type).isForall do return none
  -- If level mvars are present we abort.
  if type.hasLevelMVar then return none
  let cgr : Congr := { rel := .eq, lhs := type, rhs := .const ``True [] }
  let proof ← mkEqTrue proof
  return some { cgr with proof, src, conds := #[], mvars.lhs := {}, mvars.rhs := {}, }

def validDirs (rw : Rewrite) (cfg : Config.Erasure) : Directions :=
  -- MVars appearing in propositional conditions are definitely going to be part of the rewrite's
  -- LHS, so they can (and should be) ignored when computing valid directions.
  -- TODO: How does visibility work in conditions?
  let propCondExpr  : MVarIdSet  := rw.conds.filter (·.kind.isProof) |>.foldl (init := ∅) (·.union <| ·.mvars.visibleExpr  cfg)
  let propCondLevel : LMVarIdSet := rw.conds.filter (·.kind.isProof) |>.foldl (init := ∅) (·.union <| ·.mvars.visibleLevel cfg)
  let visibleExprLhs    := rw.mvars.lhs.visibleExpr  cfg |>.filter (!propCondExpr.contains ·)
  let visibleExprRhs    := rw.mvars.rhs.visibleExpr  cfg |>.filter (!propCondExpr.contains ·)
  let visibleLevelLhs   := rw.mvars.lhs.visibleLevel cfg |>.filter (!propCondLevel.contains ·)
  let visibleLevelRhs   := rw.mvars.rhs.visibleLevel cfg |>.filter (!propCondLevel.contains ·)
  let exprDirs          := Directions.satisfyingSuperset visibleExprLhs visibleExprRhs
  let lvlDirs           := Directions.satisfyingSuperset visibleLevelLhs visibleLevelRhs
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

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction. At some point we may want
--       to redefine `Rewrites` using a better suited data structure like `HashMap Source Rewrite`.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? (·.src == src) rws
