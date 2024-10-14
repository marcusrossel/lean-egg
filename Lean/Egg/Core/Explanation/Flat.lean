import Egg.Core.Explanation.Basic

open Lean

namespace Egg.Explanation

private def Expression.needsDefEq : Expression → Bool
  | lvl _ | proof _ => true
  | _               => false

-- Returns `none` if the subexpression position is inside a `needsDefEq` expression.
private def Expression.viewSubexpr? (e : Expression) (pos : SubExpr.Pos) : Option Expression :=
  go pos.toArray.toList e
where
  go : List Nat → Expression → Option Expression
  | [],           e                => e
  | _ :: _,       .lvl _           => none
  | _ :: _,       .sort _          => none
  | (_ + 1) :: _, .const ..        => none
  | 0 :: tl,      .app fn _        => go tl fn
  | 1 :: tl,      .app _ arg       => go tl arg
  | 0 :: tl,      .lam _ ty _      => go tl ty -- TODO: does the var count in congruence justifications?
  | 1 :: tl,      .lam _ _ body    => go tl body
  | 0 :: tl,      .forall _ ty _   => go tl ty
  | 1 :: tl,      .forall _ _ body => go tl body
  | _ :: _,       .proof _         => none
  | _,            _                => panic! s!"in 'Expression.viewSubexpr': invalid coordinate"

private def Expression.replaceSubexpr (e rep : Expression) (pos : SubExpr.Pos) : Expression :=
  go pos.toArray.toList e
where
  go : List Nat → Expression → Expression
  | [],            _                   => rep
  | ps,            .lvl l              => .lvl (replaceLvl ps l)
  | 0 :: tl,       .sort l             => .sort (replaceLvl tl l)
  | (n + 1) :: tl, .const name ls      => .const name <| ls.enum.map fun (i, l) => if i == n then (replaceLvl tl l) else l
  | 0 :: tl,       .app fn arg         => .app (go tl fn) arg
  | 1 :: tl,       .app fn arg         => .app fn (go tl arg)
  | 0 :: tl,       .lam var ty body    => .lam var (go tl ty) body -- TODO: does the var count in congruence justifications?
  | 1 :: tl,       .lam var ty body    => .lam var ty (go tl body)
  | 0 :: tl,       .forall var ty body => .forall var (go tl ty) body
  | 1 :: tl,       .forall var ty body => .forall var ty (go tl body)
  | 0 :: tl,       .proof p            => .proof (go tl p)
  | _,             _                   => panic! s!"in 'Expression.replaceSubexpr: invalid coordinate"
  replaceLvl : List Nat → Level → Level
  | 0 :: tl, .succ l     => .succ (replaceLvl tl l)
  | 0 :: tl, .max l₁ l₂  => .max (replaceLvl tl l₁) l₂
  | 1 :: tl, .max l₁ l₂  => .max l₁ (replaceLvl tl l₂)
  | 0 :: tl, .imax l₁ l₂ => .imax (replaceLvl tl l₁) l₂
  | 1 :: tl, .imax l₁ l₂ => .imax l₁ (replaceLvl tl l₂)
  | [], _ =>
    match rep with
    | .lvl l => l
    | _ => panic! s!"in 'Expression.replaceSubexpr.replaceLvl: tried to subsitute non-level 'Expression'"
  | _, _ => panic! s!"in 'Expression.replaceSubexpr.replaceLvl: invalid coordinate"

structure Flat.Step extends Rewrite.Descriptor where
  dst : Expression
  pos : SubExpr.Pos

protected structure Flat where
  start : Expression
  steps : List Flat.Step

inductive Error where
  | nonDefEqPrimitiveRw

namespace FlattenM

private structure State where
  head       : Expression
  pos        : SubExpr.Pos
  symm       : Bool
  needsDefEq : Bool

private abbrev _root_.Egg.Explanation.FlattenM := ExceptT Error <| StateM FlattenM.State

def symm : FlattenM Bool := State.symm <$> get

def withToggledSymm (m : FlattenM α) : FlattenM α := do
  let s ← get
  modify ({ · with symm := !s.symm })
  let res ← m
  modify ({ · with symm := s.symm })
  return res

def withMove (subpos : Nat) (m : FlattenM α) : FlattenM α := do
  let { head, pos, needsDefEq, .. } ← get
  -- If the subexpression is inside a `needsDefEq` expression (if `viewSubexpr?` is `none`), we need
  -- defeq, too.
  let de := if let some e := head.viewSubexpr? pos then e.needsDefEq else true
  modify ({ · with pos := pos.push subpos, needsDefEq := de || needsDefEq })
  let res ← m
  modify ({ · with pos, needsDefEq })
  return res

def mkStep (descr : Rewrite.Descriptor) (lhs rhs : Expression) : FlattenM Flat.Step := do
  let { head, pos, symm, needsDefEq } ← get
  let (dir, subDst) := if symm then (descr.dir.opposite, lhs) else (descr.dir, rhs)
  if (needsDefEq || subDst.needsDefEq) && !descr.src.isDefEq then throw .nonDefEqPrimitiveRw
  let dst := head.replaceSubexpr subDst pos
  modify ({ · with head := dst })
  -- TODO: The `pos` might be off for `proof` constructs when used during proof reconstruction,
  --       because we used to ignore when determining the position during parsing.
  return { descr with dir, pos, dst }

end FlattenM

open FlattenM in
partial def flatten (expl : Explanation) : Except Error Explanation.Flat := do
  let (steps?, _) := go expl.target |>.run
    { head := expl.target.lhs, pos := .root, symm := false, needsDefEq := false }
  return { start := expl.target.lhs, steps := ← steps? }
where
  go (lem : Lemma) : FlattenM (List Flat.Step) := do
    match lem.jus with
    | .rw descr    => return [← mkStep descr lem.lhs lem.rhs]
    | .rfl         => return []
    | .symm l      => withToggledSymm do go expl.lemmas[l]!
    | .trans l₁ l₂ =>
      if ← symm
      then return (← go expl.lemmas[l₂]!).reverse ++ (← go expl.lemmas[l₁]!).reverse
      else return (← go expl.lemmas[l₁]!)         ++ (← go expl.lemmas[l₂]!)
    | .congr ls =>
      ls.toList.enum.foldlM (init := [])
        fun steps (subpos, lem) => withMove subpos do return steps ++ (← go expl.lemmas[lem]!)
