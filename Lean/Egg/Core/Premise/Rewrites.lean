import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Ambient
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

-- Condition can become proven during type class specialization. We still need to keep these
-- conditions in order to use their `expr` during proof reconstruction. Proven conditions are not
-- encoded and thus transparent to the backend though.
def Condition.isProven (cond : Condition) : Bool :=
  !cond.expr.isMVar

def Condition.instantiateMVars (cond : Condition) : MetaM Condition := do
  return { cond with
    expr  := ← Lean.instantiateMVars cond.expr
    type  := ← Lean.instantiateMVars cond.type
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

structure Config extends Config.Normalization where
  amb         : MVars.Ambient
  eraseProofs : Bool

instance : Coe Config Config.Normalization where
  coe := Config.toNormalization

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
  let mLhs := (← MVars.collect cgr.lhs cfg.eraseProofs).remove cfg.amb
  let mRhs := (← MVars.collect cgr.rhs cfg.eraseProofs).remove cfg.amb
  let conds ← collectConds args mLhs mRhs
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs }
where
  -- The interaction between proof erasure and conditional rewrites is somewhat finicky. Without
  -- proof erasure, a hypothesis `h` of a rewrite is not considered a precondition if it appears in
  -- the rewrite's equation. Naively, proof erasure breaks this as it erases `h` from the equation
  -- (which thus becomes a precondition, even when it is completely determined by the equation).
  -- Thus, we handle proof terms specially in `MVars.collect` by collecting both the proof term
  -- mvars and the corresponding proposition mvars. We then make sure to add the proof term mvars to
  -- the `noCond` set, even when proof erasure is active.
  collectConds (args : Array Expr) (mLhs mRhs : Egg.MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    let mut noCond ← typeMVarClosure (mLhs.expr.merge mRhs.expr)
    if cfg.eraseProofs then noCond := noCond.merge mLhs.proof |>.merge mRhs.proof
    for arg in args do
      if noCond.contains arg.mvarId! then continue
      let ty ← arg.mvarId!.getType
      let mvars := (← MVars.collect ty cfg.eraseProofs).remove cfg.amb
      conds := conds.push { expr := arg, type := ty, mvars }
    return conds
  typeMVarClosure (init : MVarIdSet) : MetaM MVarIdSet := do
    let mut closure : MVarIdSet := ∅
    let mut todos := init
    let mut nextTodo? := todos.min
    while h : nextTodo?.isSome do
      let m := nextTodo?.get h
      todos := todos.erase m
      closure := closure.insert m
      todos := todos.merge (← MVars.collect (← m.getType) cfg.eraseProofs).expr
      nextTodo? := todos.min
    return closure

def isConditional (rw : Rewrite) : Bool :=
  !rw.conds.isEmpty

def validDirs (rw : Rewrite) : Directions :=
  let exprDirs := Directions.satisfyingSuperset rw.mvars.lhs.expr rw.mvars.rhs.expr
  let lvlDirs  := Directions.satisfyingSuperset rw.mvars.lhs.lvl rw.mvars.rhs.lvl
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
      let (_, s) ← (← MVars.collect cond.expr (proofErasure := false)).fresh (init := subst)
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

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
