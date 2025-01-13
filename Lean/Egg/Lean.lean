import Lean
import Std

def List.replicateM [Monad m] (count : Nat) (f : m α) : m (List α) := do
  let mut result := []
  for _ in [0:count] do
    result := result.concat (← f)
  return result

-- From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/sorting.20in.20monad/near/473162379
partial def List.qsortM [Monad m] (comp : α → α → m Bool) [BEq α] : List α → m (List α )
  | [] => return []
  | x :: xs => do
    let (fst, lst) ← xs.partitionM fun t => comp t x
    return (← fst.qsortM comp) ++ [x] ++ (← lst.qsortM comp)

partial def String.lineCount (s : String) : Nat :=
  go 0 0
where
  go (pos : Pos) (count : Nat) : Nat :=
    if s.atEnd pos then
      count
    else
      let inc := if (s.get pos) == '\n' then 1 else 0
      go (s.next pos) (count + inc)

namespace Std.HashMap

variable [BEq α] [Hashable α]

def merge (m₁ m₂ : HashMap α β) (combine : β → β → β) : HashMap α β := Id.run do
  let mut m := m₁
  for (a, b) in m₂ do
    m := m₁.alter a fun b'? =>
      if let some b' := b'? then combine b' b else b
  return m₁

def filterM [Monad m] (map : HashMap α β) (keep : α → m Bool) : m (HashMap α β) :=
  map.foldM (init := map) fun result a _ => do
    if ← keep a then return result else return result.erase a

end Std.HashMap

namespace Lean

/-
This terminates because the types of mvars aren't simply mvars again:
```
#eval do
  let m ← mkFreshExprMVar none
  logInfo m -- ?m.3
  let m ← m.mvarId!.getType
  logInfo m -- ?m.2
  let .sort m ← m.mvarId!.getType | failure
  logInfo m -- ?u.1
```
-/
partial def MVarIdSet.typeMVarClosure (init ignore : MVarIdSet) : MetaM MVarIdSet := do
  let mut closure : MVarIdSet := ∅
  let mut todos := init
  let mut nextTodo? := todos.min
  while h : nextTodo?.isSome do
    let m := nextTodo?.get h
    todos := todos.erase m
    unless ignore.contains m do
      closure := closure.insert m
      let { result, .. } := (← m.getType).collectMVars {}
      for r in result do todos := todos.insert r
    nextTodo? := todos.min
  return closure

instance : Singleton MVarId MVarIdSet where
  singleton m := (∅ : MVarIdSet).insert m

def Meta.isTCInstance (e : Expr) : MetaM Bool :=
  return (← isClass? <| ← inferType e).isSome

-- From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Extending.20tacticSeqs/near/474553725
open Elab Parser Tactic in
def mkTacticSeqPrepend (t : TSyntax `tactic) : TSyntax ``tacticSeq → TermElabM (TSyntax ``tacticSeq)
  | `(tacticSeq|{ $[$tacs:tactic]* }) => `(tacticSeq|{ $[$(#[t] ++ tacs)]* })
  | `(tacticSeq|$[$tacs:tactic]*)     => `(tacticSeq|$[$(#[t] ++ tacs)]*)
  | _ => throwError "unknown syntax"

-- From Batteries: `MVarId.assignIfDefeq`
open Meta in
def MVarId.assignIfDefeq' (g : MVarId) (e : Expr) : MetaM Unit := do
  guard <| ← isDefEq (← g.getType) (← inferType e)
  g.checkNotAssigned `assignIfDefeq
  g.assign e

-- Note: The `_uniq` prefix comes from the `NameGenerator`.

-- Note that loose fvars' names are pretty printed using the `_fvar` prefix, but the underlying name
-- still uses the `_uniq` prefix:
-- https://github.com/leanprover/lean4-nightly/blob/d569ed4e5f796bbabbe17302a7c5a7060a4c7de7/src/Lean/PrettyPrinter/Delaborator/Builtins.lean#L33
def FVarId.uniqueIdx! : FVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique fvar-id"

def FVarId.fromUniqueIdx (idx : Nat) : FVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

def MVarId.uniqueIdx! : MVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique mvar-id"

def MVarId.fromUniqueIdx (idx : Nat) : MVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

-- Note that level mvars' names are pretty printed using the `?u` prefix, but the underlying name
-- still uses the `_uniq` prefix:
-- https://github.com/leanprover/lean4/blob/e206e53f4e37ecd810b2de36b7544240d579c535/src/Lean/Level.lean#L436
def LMVarId.uniqueIdx! : LMVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique level mvar-id"

def LMVarId.fromUniqueIdx (idx : Nat) : LMVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

deriving instance BEq, Hashable for SubExpr.Pos

def RBTree.filterM [Monad m] (t : RBTree α cmp) (keep : α → m Bool) : m (RBTree α cmp) :=
  t.foldM (init := t) fun res a => return if ← keep a then res else res.erase a

def RBTree.map (t : RBTree α cmp) (f : α → α) : RBTree α cmp :=
  t.fold (init := ∅) fun res a => res.insert (f a)

def RBTree.subtract (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₁.filter (!t₂.contains ·)

def RBTree.singleton (a : α) : RBTree α cmp :=
  insert ∅ a
