import Egg.Lean
import Egg.Core.Config
import Lean

open Lean hiding HashMap HashSet
open Meta
open Std (HashMap HashSet)

namespace Egg.MVars

-- TODO: We need to consider how `Eq` and `Iff` are encoded.

/-
1. An mvar is `unconditionallyVisible` if it appears explicitly in the given expression, but not in
   a type class instance or proof term. For example, this holds for `?m` in `f (?m + 1)`.
2. An mvar `isTcInst` if its type is a type class. For example, this holds for `?i` in
   `@Add Nat ?i`.
3. An mvar is `inTcInstTerm` if it appears explicitly in a term whose type is a type class. For
   example, this holds for both `?t` and `?i` in `@instHAdd ?t ?i`.
4. An mvar is `inErasedTcInst` if it appears explicitly in the type of a term whose type is a type
   class. For example, this holds for `?t` but not for `?i` in `@instHAdd ?t ?i`. The type of this
   instance is `HAdd ?t ?t ?t`.
5. An mvar is `inProofTerm` if it appears explicitly in a term whose type is a proposition. For
   example, this holds for `?m` and `?n` in `Nat.add_comm ?m ?n`.
6. An mvar is `inErasedProof` if it appears explicitly in the type of a term whose type is a
   proposition. For example, this holds for `?m` and `?n` in `Nat.add_comm ?m ?n`. The type of this
   proof is `?m + ?n = ?n + ?m`.

A commonly required composite property is whether an mvar will appear in the final encoded term. We
say that such an mvar is "visible". Visibility depends on Properties 1, 3, 4, 5 and 6, as well as
the erasure configuration. The visibility property is used for the following:
* To implement explosion.
* To determine the valid directions of a rewrite.
* To determine which mvars are conditions of a rewrite.
* To determine whether a given condition of a conditional rewrite is unbounded.

Other use cases of properties are:
* To determine which mvars are conditions of a rewrite, we also need to use Properties 1, 3 and 5.
* Type class specialization needs Property 2.
-/
inductive Property where
  | unconditionallyVisible
  | isTcInst
  | inTcInstTerm
  | inErasedTcInst
  | inProofTerm
  | inErasedProof
  deriving BEq, Hashable

abbrev Properties := HashSet Property

namespace Properties

def isVisible (ps : Properties) (cfg : Config.Erasure) : Bool :=
  ps.contains .unconditionallyVisible
  || (ps.contains .inTcInstTerm   && !cfg.eraseTCInstances)
  || (ps.contains .inErasedTcInst && cfg.eraseTCInstances)
  || (ps.contains .inProofTerm    && !cfg.eraseProofs)
  || (ps.contains .inErasedProof  && cfg.eraseProofs)

def inTarget (ps : Properties) : Bool :=
  ps.contains .unconditionallyVisible
  || ps.contains .inProofTerm
  || ps.contains .inTcInstTerm

def insertIf (ps : Properties) (condition : Bool) (p : Property) : Properties :=
  if condition then ps.insert p else ps

end Properties

structure _root_.Egg.MVars where
  expr : HashMap  MVarId Properties := ∅
  lvl  : HashMap LMVarId Properties := ∅
  deriving Inhabited

def visibleExpr (mvars : MVars) (cfg : Config.Erasure) : MVarIdSet :=
  mvars.expr.fold (init := ∅) fun result m ps =>
    if ps.isVisible cfg then result.insert m else result

def visibleLevel (mvars : MVars) (cfg : Config.Erasure) : LMVarIdSet :=
  mvars.lvl.fold (init := ∅) fun result m ps =>
    if ps.isVisible cfg then result.insert m else result

def tcInsts (mvars : MVars) : MVarIdSet :=
  mvars.expr.fold (init := ∅) fun result m ps =>
    if ps.contains .isTcInst then result.insert m else result

def inTarget (mvars : MVars) : MVarIdSet :=
  mvars.expr.fold (init := ∅) fun result m ps =>
    if ps.inTarget then result.insert m else result

def insertExpr (mvars : MVars) (m : MVarId) (ps : Properties) : MVars :=
  { mvars with expr := mvars.expr.alter m (ps.union <| ·.getD ∅) }

def insertLevel (mvars : MVars) (m : LMVarId) (ps : Properties) : MVars :=
  { mvars with lvl := mvars.lvl.alter m (ps.union <| ·.getD ∅) }

def merge (vars₁ vars₂ : MVars) : MVars where
  expr  := vars₁.expr.merge vars₂.expr .union
  lvl   := vars₁.lvl.merge  vars₂.lvl  .union

def removeAssigned (mvars : MVars) : MetaM MVars :=
  return {
    expr := ← mvars.expr.filterM fun var => return !(← var.isAssigned)
    lvl  := ← mvars.lvl.filterM  fun var => return !(← isLevelMVarAssigned var)
  }
