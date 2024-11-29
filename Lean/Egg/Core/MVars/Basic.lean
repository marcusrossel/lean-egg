import Egg.Lean
import Egg.Core.Config
import Lean
open Lean Meta

namespace Egg

-- PROBLEM: The point of the `tc` mvars is to know which type class instance mvars exist in a term,
--          so that we can generate specializations. When there's no erasure, this is
--          quite simply a subset of `expr`.
--          When proof erasure is active, we don't collect any of the type class instance mvars in
--          the proof term, and instead *do* collect those appearing in the erasure term (the
--          proof's type).
--          When type class instance erasure is active, we don't collect any of the type class
--          instance mvars in the type class instance term, and instead *do* collect those appearing
--          in the erasure term (the type class instance's type).
--          In the latter case we run into the problem that this behavior entails that `tc = ∅` when
--          type class instance erasure is active, which in turn means that we don't get any type
--          class specialization rewrites.

structure MVars where
  expr : MVarIdSet
  lvl : LMVarIdSet
  -- The subset of `expr` of mvars whose type is a type class.
  tc : MVarIdSet
  -- The set of mvars which appear in proof terms. This is only populated if `MVars.collect` is
  -- called with `proofErasure := true`. Note that it is not necessarily (and likely not) a subset
  -- of `expr`, as inserting an mvar into this set does not mean that it is inserted into `expr`.
  proof : MVarIdSet
  -- The set of mvars which appear in type class instances. This is only populated if
  -- `MVars.collect` is called with `tcInstanceErasure := true`. Note that it is not necessarily
  -- (and likely not) a subset of `expr`, as inserting an mvar into this set does not mean that it
  -- is inserted into `expr`.
  inst : MVarIdSet
  deriving Inhabited

-- Note: We use an `EmptyCollection` instead of giving each field a default value of `∅` so we see
--       where code breaks when we add new fields (e.g. in `merge` below).
instance : EmptyCollection MVars where
  emptyCollection := ⟨∅, ∅, ∅, ∅, ∅⟩

private def MVars.insertIfTCInstance (mvars : MVars) (id : MVarId) : MetaM MVars := do
  if ← Meta.isTCInstance (.mvar id)
  then return { mvars with tc := mvars.tc.insert id }
  else return mvars

private structure MVarCollectionState where
  visitedExprs : ExprSet  := {}
  visitedLvls  : LevelSet := {}
  mvars        : MVars    := {}

inductive ErasureTarget? where
  | proof
  | inst
  | none

private partial def collectMVars (e : Expr) (s : MVarCollectionState) (cfg : Config.Erasure) :
    MetaM MVarCollectionState := do
  if ← (return cfg.eraseProofs) <&&> (Meta.isProof e) then
    let s' ← core (insideErased := .proof) e s
    core (insideErased := .none) (← inferType e) s'
  else if ← (return cfg.eraseTCInstances) <&&> (Meta.isTCInstance e) then
    let s' ← core (insideErased := .inst) e s
    core (insideErased := .none) (← inferType e) s'
  else
    core (insideErased := .none) e s
where
  core (insideErased : ErasureTarget?) : Expr → MVarCollectionState → MetaM MVarCollectionState
    | .mvar id =>
      visitMVar insideErased id
    | .const _ lvls =>
      (return visitConst insideErased lvls ·)
    | .sort lvl =>
      (return visitSort insideErased lvl ·)
    | .proj _ _ e | .mdata _ e =>
      visit insideErased e
    | .forallE _ e₁ e₂ _ | .lam _ e₁ e₂ _ | .app e₁ e₂ =>
      (withLocalDecl .anonymous .default e₁ fun fvar =>
        (visit insideErased e₁ >=> visit insideErased (e₂.instantiate #[fvar])) ·)
    | .letE _ e₁ e₂ e₃ _ =>
      (withLocalDecl .anonymous .default e₁ fun fvar =>
        (visit insideErased e₁ >=> visit insideErased e₂ >=> visit insideErased (e₃.instantiate #[fvar])) ·)
    | _ => pure

  visit (insideErased : ErasureTarget?) (e : Expr) (s : MVarCollectionState) :
      MetaM MVarCollectionState :=
    if !e.hasMVar || s.visitedExprs.contains e then
      return s
    else
      let s' := { s with visitedExprs := s.visitedExprs.insert e }
      match insideErased with
      | .none  => collectMVars e s' cfg
      | target => core (insideErased := target) e s'

  visitMVar (insideErased : ErasureTarget?) (id : MVarId) (s : MVarCollectionState) :
      MetaM MVarCollectionState := do
    match insideErased with
    | .proof => return { s with mvars.proof := s.mvars.proof.insert id }
    | .inst  => return { s with mvars.inst := s.mvars.inst.insert id }
    | .none  =>
      let s := { s with mvars.expr := s.mvars.expr.insert id }
      return { s with mvars := ← s.mvars.insertIfTCInstance id }

  visitConst (erasing : ErasureTarget?) (lvls : List Level) (s : MVarCollectionState) :
      MVarCollectionState :=
    -- We only consider the levels in non-erased expressions, as erased expressions' levels won't
    -- appear in the final expression. Instead, their types' levels will, which is covered when we
    -- do this traversal for the erased expressions' types.
    match erasing with
    | .proof | .inst => s
    | .none => Id.run do
      let mut s := s
      for lvl in lvls do
        if s.visitedLvls.contains lvl then
          continue
        else
          s := { s with
            mvars.lvl := lvl.collectMVars s.mvars.lvl
            visitedLvls := s.visitedLvls.insert lvl
          }
      return s

  visitSort (erasing : ErasureTarget?) (lvl : Level) (s : MVarCollectionState) :
      MVarCollectionState :=
    -- We only consider the levels in non-erased expressions, as erased expressions' levels won't
    -- appear in the final expression. Instead, their types' levels will, which is covered when we
    -- do this traversal for the erased expressions' types.
    match erasing with
    | .proof | .inst => s
    | .none =>
      if s.visitedLvls.contains lvl then
        s
      else
        { s with
          mvars.lvl := lvl.collectMVars s.mvars.lvl
          visitedLvls := s.visitedLvls.insert lvl
        }

namespace MVars

def collect (e : Expr) (cfg : Config.Erasure) : MetaM MVars :=
  MVarCollectionState.mvars <$> collectMVars e {} cfg

def merge (vars₁ vars₂ : MVars) : MVars where
  expr  := vars₁.expr.merge vars₂.expr
  lvl   := vars₁.lvl.merge vars₂.lvl
  tc    := vars₁.tc.merge vars₂.tc
  proof := vars₁.proof.merge vars₂.proof
  inst  := vars₁.inst.merge vars₂.inst

def removeAssigned (mvars : MVars) : MetaM MVars := do
  return {
    expr  := ← mvars.expr.filterM  fun var => return !(← var.isAssigned)
    lvl   := ← mvars.lvl.filterM   fun var => return !(← isLevelMVarAssigned var)
    tc    := ← mvars.tc.filterM    fun var => return !(← var.isAssigned)
    proof := ← mvars.proof.filterM fun var => return !(← var.isAssigned)
    inst  := ← mvars.inst.filterM  fun var => return !(← var.isAssigned)
  }
