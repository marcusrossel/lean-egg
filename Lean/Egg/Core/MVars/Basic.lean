import Egg.Lean
import Egg.Core.Config
import Lean

open Lean Std Meta

namespace Egg.MVars

/-
1. An mvar is `unconditionallyVisible` if it appears explicitly in the given expression, but not in
   a type class instance or proof term. For example, this holds for `?m` in `f (?m + 1)`.
2. An mvar `isTcInst` if its type is a type class. For example, this holds for `?i` in
   `@Add Nat ?i`.
3. An mvar is `inTcInstTerm` if it appears explicitly in a term whose type is a type class. For
   example, this holds for both `?t` and `?i` in `@instHAdd ?t ?i`, but not for `?i` by itself.
4. An mvar is `inErasedTcInst` if it appears explicitly in the type of a term whose type is a type
   class. For example, this holds for `?t` but not for `?i` in `@instHAdd ?t ?i`. The type of this
   instance is `HAdd ?t ?t ?t`.
5. An mvar is `inProofTerm` if it appears explicitly in a term whose type is a proposition. For
   example, this holds for `?m` and `?n` in `Nat.add_comm ?m ?n`.
6. An mvar is `inErasedProof` if it appears explicitly in the type of a term whose type is a
   proposition. For example, this holds for `?m` and `?n` in `Nat.add_comm ?m ?n`. The type of this
   proof is `?m + ?n = ?n + ?m`.
7. An mvar is `inEqType` if it is the universe level or type argument of an `Eq`. For example, this
   holds for `?u` and `?t` in `@Eq.{?u} ?t ?a ?b`. Note that we don't set this property for `Iff`,
   as `Iff` has neither a universe level nor a type argument.

A commonly required composite property is whether an mvar will appear in the final encoded term. We
say that such an mvar is "visible". Visibility depends on Properties 1, 4, and 6. The visibility
property is used for the following:
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
  | isProof
  | inProofTerm
  | inErasedProof
  | inEqType
  deriving BEq, Hashable

def Property.isVisible : Property → Bool
  | unconditionallyVisible | inErasedTcInst | inErasedProof => true
  | _                                                       => false

abbrev Properties := HashSet Property

namespace Properties

def isVisible (ps : Properties) : Bool :=
  ps.any (·.isVisible)

def insertIf (ps : Properties) (condition : Bool) (p : Property) : Properties :=
  if condition then ps.insert p else ps

end Properties

structure _root_.Egg.MVars where
  expr : HashMap  MVarId Properties := ∅
  lvl  : HashMap LMVarId Properties := ∅
  deriving Inhabited

def isEmpty (mvars : MVars) : Bool :=
  mvars.expr.isEmpty && mvars.lvl.isEmpty

def visibleExpr (mvars : MVars) : MVarIdSet :=
  mvars.expr.fold (init := ∅) fun result m ps =>
    if ps.isVisible then result.insert m else result

def visibleLevel (mvars : MVars) : LMVarIdSet :=
  mvars.lvl.fold (init := ∅) fun result m ps =>
    if ps.isVisible then result.insert m else result

def tcInsts (mvars : MVars) : MVarIdSet :=
  mvars.expr.fold (init := ∅) fun result m ps =>
    if ps.contains .isTcInst then result.insert m else result

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
