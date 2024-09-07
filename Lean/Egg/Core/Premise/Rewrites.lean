import Egg.Core.Directions
import Egg.Core.MVars.Subst
import Egg.Core.MVars.Ambient
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg

structure Rewrite.MVars where
  lhs : MVars
  rhs : MVars
  deriving Inhabited

structure Rewrite.Condition where
  expr  : Expr -- Without instantiation, this is an mvar.
  type  : Expr
  mvars : Egg.MVars

def Rewrite.Condition.instantiateMVars (cond : Condition) : MetaM Condition := do
  return { cond with
    expr  := ← Lean.instantiateMVars cond.expr
    type  := ← Lean.instantiateMVars cond.type
    mvars := ← cond.mvars.removeAssigned
  }

-- Note: We don't create `Rewrite`s directly, but use `Rewrite.from` instead.
structure Rewrite extends Congr where
  private mk ::
  proof : Expr
  src   : Source
  conds : Array Rewrite.Condition
  mvars : Rewrite.MVars
  deriving Inhabited

namespace Rewrite

structure Config where
  norm? : Option Config.Normalization := none
  amb   : MVars.Ambient

-- TODO: We're not taking proof erasure into account when determining mvars.
partial def from? (proof type : Expr) (src : Source) (cfg : Config) : MetaM (Option Rewrite) := do
  let type ← if let some norm := cfg.norm? then normalize type norm else pure type
  let mut (args, _, eqOrIff?) ← forallMetaTelescope type
  let some cgr ← Congr.from? eqOrIff? | return none
  let proof := mkAppN proof args
  let mLhs := (← MVars.collect cgr.lhs).remove cfg.amb
  let mRhs := (← MVars.collect cgr.rhs).remove cfg.amb
  let conds ← collectConds args mLhs mRhs
  return some { cgr with proof, src, conds, mvars.lhs := mLhs, mvars.rhs := mRhs }
where
  collectConds (args : Array Expr) (mLhs mRhs : Egg.MVars) : MetaM (Array Rewrite.Condition) := do
    let mut conds := #[]
    let noCond ← typeMVarClosure (mLhs.expr.merge mRhs.expr)
    for arg in args do
      if noCond.contains arg.mvarId! then continue
      let ty ← arg.mvarId!.getType
      conds := conds.push { expr := arg, type := ty, mvars := (← MVars.collect ty).remove cfg.amb }
    return conds
  typeMVarClosure (init : MVarIdSet) : MetaM MVarIdSet := do
    let mut closure : MVarIdSet := ∅
    let mut todos := init
    let mut nextTodo? := todos.min
    while h : nextTodo?.isSome do
      let m := nextTodo?.get h
      todos := todos.erase m
      closure := closure.insert m
      todos := todos.merge (← MVars.collect <| ← m.getType).expr
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
      let (m, s) ← MVars.freshExpr cond.expr.mvarId! (init := subst)
      let (mvars, s) ← cond.mvars.fresh (init := s)
      conds := conds.push { expr := .mvar m, type := s.apply cond.type, mvars }
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
    lhs         := ← Lean.instantiateMVars rw.lhs
    rhs         := ← Lean.instantiateMVars rw.rhs
    proof       := ← Lean.instantiateMVars rw.proof
    mvars.lhs   := ← rw.mvars.lhs.removeAssigned
    mvars.rhs   := ← rw.mvars.rhs.removeAssigned
    conds       := ← rw.conds.mapM (·.instantiateMVars)
  }

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
