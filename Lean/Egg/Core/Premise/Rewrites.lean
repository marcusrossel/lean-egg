import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Collect
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean

open Lean hiding HashSet
open Meta Std

namespace Egg.Rewrite

protected structure MVars where
  lhs : MVars
  rhs : MVars
  all : MVarIdSet
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
  let all   ← collectAllMVars args mLhs mRhs
  let conds ← collectConds all
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs, mvars.all := all }
where
  -- Note: The set of all relevant mvars is not only that contained in `mLhs` and `mRhs`, but also
  --       those in `args`! For example in `∀ (n) (h : n ≠ 0), n / n = 1`, the variable `h` is only
  --       in `args`, and not in the body mvars. However, note also that `args` does not necessarily
  --       contain all mvars, because elaboration sometimes causes some quantified variables to
  --       already be instantiated as mvars.
  collectAllMVars (args : Array Expr) (mLhs mRhs : MVars) : MetaM MVarIdSet := do
    let mut result := ∅
    for m in mLhs.expr.keys do result := result.insert m
    for m in mRhs.expr.keys do result := result.insert m
    for m in args           do result := result.insert m.mvarId!
    return result
  collectConds (mvars : MVarIdSet) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    for m in mvars do
      let type ← m.getType
      let some kind ← Condition.Kind.forType? type | continue
      let mvars ← MVars.collect type
      conds := conds.push { kind, expr := (.mvar m), type, mvars }
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
  return some { cgr with proof, src, conds := #[], mvars.lhs := {}, mvars.rhs := {}, mvars.all := {} }

def validDirs (rw : Rewrite) (conditionSubgoals : Bool) : MetaM Directions := do
  let mut proofVars := ∅
  let mut visibleProofTypeVars := ∅
  let mut typeClassVars := ∅
  for cond in rw.conds do
    if cond.isProven then continue
    match cond.kind with
    | .proof =>
      if conditionSubgoals then continue
      proofVars := proofVars.insert cond.expr.mvarId!
      visibleProofTypeVars := visibleProofTypeVars.union cond.mvars.visibleExpr
    | .tcInst =>
      typeClassVars := typeClassVars.insert cond.expr.mvarId!
  let forward  ← isValidWithLhsRhs rw.mvars.lhs rw.mvars.rhs rw.mvars.all proofVars visibleProofTypeVars typeClassVars
  let backward ← isValidWithLhsRhs rw.mvars.rhs rw.mvars.lhs rw.mvars.all proofVars visibleProofTypeVars typeClassVars
  let exprDirs := Directions.ofBool forward backward
  return exprDirs
  -- TODO: Levels. Should follow the same rules as expr mvars, shouldnt they?
  -- let lvlDirs := sorry
  -- return exprDirs.meet lvlDirs
where
  isValidWithLhsRhs
      (lhs rhs : MVars) (all : MVarIdSet)
      (proofVars visibleProofTypeVars typeClassVars : MVarIdSet) : MetaM Bool := do
    -- Checks that the LHS variables are a superset of the RHS variables.
    for mvar in rhs.visibleExpr do
      unless lhs.visibleExpr.contains mvar || visibleProofTypeVars.contains mvar do return false
    -- Checks that the variables appearing in type class conditions are matched.
    for cond in rw.conds do
      for mvar in cond.mvars.expr.keys do
        unless lhs.visibleExpr.contains mvar || visibleProofTypeVars.contains mvar do return false
    -- When condition subgoals are enabled, covering does not include proof conditions and we don't
    -- require variables appearing in proof conditions to be covered.
    if conditionSubgoals then
      -- Constructs ω(ℒ(t) ∪ 𝒞(t)).
      let mut covered := lhs.visibleExpr
      for mvar in typeClassVars do covered := covered.insert mvar
      covered ← covered.typeMVarClosure
      let exempt ← proofVars.typeMVarClosure
      return (all.diff exempt).subset covered
    else
      -- Constructs ω(ℒ(t) ∪ 𝒫(t) ∪ 𝒞(t)).
      let mut covered := lhs.visibleExpr
      for mvar in typeClassVars do covered := covered.insert mvar
      for mvar in proofVars     do covered := covered.insert mvar
      covered ← covered.typeMVarClosure
      return all.subset covered

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
  let (all, subst)   ← freshAll (init := subst)
  let rw' := { rw with
    src
    lhs   := subst.apply rw.lhs
    rhs   := subst.apply rw.rhs
    proof := subst.apply rw.proof
    conds := conds
    mvars.lhs := mLhs
    mvars.rhs := mRhs
    mvars.all := all
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
  freshAll (init : MVars.Subst) : MetaM (MVarIdSet × MVars.Subst) := do
    let mut subst := init
    let mut all := ∅
    for mvar in rw.mvars.all do
      let (m, s) ← (← MVars.collect (.mvar mvar)).fresh (init := subst)
      all := all.insert m.expr.keys[0]!
      subst := s
    return (all, subst)

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
    mvars.all := ← rw.mvars.all.filterM fun var => return !(← var.isAssigned)
    conds     := ← rw.conds.mapM (·.instantiateMVars)
  }

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
