import Egg.Core.Explanation.Parse.Shared
import Lean
open Lean Meta

namespace Egg.Explanation.Slotted

private inductive Expression where
  | bvar   (name : String)
  | fvar   (id : FVarId)
  | mvar   (id : MVarId)
  | sort   (lvl : Level)
  | const  (name : Name) (lvls : List Level)
  | app    (fn arg : Expression)
  | lam    (var : String) (ty body : Expression)
  | forall (var : String) (ty body : Expression)
  | lit    (l : Literal)
  | proof  (prop : Expression)
  | subst  (var : String) (to e : Expression)
  | unknown
  deriving Inhabited

private structure ToExprM.State where
  bvars  : Std.HashMap String Expr
  substs : Std.HashMap String Expr

private abbrev ToExprM := StateT ToExprM.State MetaM

private def ToExprM.mapBVar (bvarId : String) : ToExprM Expr := do
  let { bvars, substs } ← get
  if let some subst := substs[bvarId]? then
    return subst
  else if let some fvar := bvars[bvarId]? then
    return fvar
  else
    throwError s!"'Egg.Explanation.ToExprM.mapBVar' received loose bvar {bvarId}"

private def ToExprM.withBinding (var : String) (type : Expr) (m : Expr → ToExprM α) : ToExprM α :=
  withLocalDecl (.mkStr1 var) .default type fun fvar => do
    let bvars := (← get).bvars
    modify fun s => { s with bvars := s.bvars.insert var fvar }
    let result ← m fvar
    modify fun s => { s with bvars }
    return result

private def ToExprM.withSubst (var : String) (e : Expr) (m : ToExprM α) : ToExprM α := do
  let substs := (← get).substs
  modify fun s => { s with substs := s.substs.insert var e }
  let result ← m
  modify fun s => { s with substs }
  return result

open ToExprM in
private def Expression.toExpr (e : Expression) : MetaM Expr :=
  Prod.fst <$> (go e).run {  bvars := ∅, substs := ∅ }
where
  go : Expression → ToExprM Expr
  | bvar id             => mapBVar id
  | fvar id             => return .fvar id
  | mvar id             => return .mvar id
  | sort l              => return .sort l
  | const name lvls     => return .const name lvls
  | app fn arg          => return .app (← go fn) (← go arg)
  | lam var ty body     => do withBinding var (← go ty) fun fvar => do mkLambdaFVars #[fvar] (← go body)
  | .forall var ty body => do withBinding var (← go ty) fun fvar => do mkForallFVars #[fvar] (← go body)
  | lit l               => return .lit l
  | proof prop          => do mkFreshExprMVar (← toExpr prop)
  | subst var to e      => do withSubst var (← go to) do go e
  | unknown             => mkFreshExprMVar none

declare_syntax_cat slot
declare_syntax_cat slotted_lvl
declare_syntax_cat slotted_expr
declare_syntax_cat slotted_expl

-- HACK: Dealing with "$" is non-trivial.
syntax num   : slot
syntax ident : slot

syntax num                                               : slotted_lvl
syntax "(" &"uvar" num ")"                               : slotted_lvl
syntax "(" &"param" str ")"                              : slotted_lvl
syntax "(" &"succ" slotted_lvl ")"                       : slotted_lvl
syntax "(" &"max" slotted_lvl slotted_lvl ")"            : slotted_lvl
syntax "(" &"imax" slotted_lvl slotted_lvl ")"           : slotted_lvl
syntax "(" &"Rewrite" noWs rw_dir rw_src slotted_lvl ")" : slotted_lvl

-- TODO: How should you parse slots?
syntax "(" &"bvar" slot ")"                               : slotted_expr
syntax "(" &"fvar" num ")"                                : slotted_expr
syntax "(" &"mvar" num ")"                                : slotted_expr
syntax "(" &"sort" slotted_lvl ")"                        : slotted_expr
syntax "(" &"const" str slotted_lvl* ")"                  : slotted_expr
syntax "(" &"app" slotted_expr slotted_expr ")"           : slotted_expr
syntax "(" &"λ" slot slotted_expr slotted_expr ")"        : slotted_expr
syntax "(" &"∀" slot slotted_expr slotted_expr ")"        : slotted_expr
syntax "(" &"lit" lit ")"                                 : slotted_expr
syntax "(" &"proof" slotted_expr ")"                      : slotted_expr
syntax "(" &"↦" slot slotted_expr slotted_expr ")"        : slotted_expr
syntax &"_"                                               : slotted_expr
syntax "(" &"Rewrite" noWs rw_dir rw_src slotted_expr ")" : slotted_expr

syntax slotted_expr+ : slotted_expl

private partial def parseSlot : (TSyntax `slot) → String
  | `(slot|$n:num)   => s!"{n.getNat}"
  | `(slot|$i:ident) => s!"{i.getId.toString (escape := false)}"
  | _                => unreachable!

private partial def parseLevel : (TSyntax `slotted_lvl) → ParseStepM Level
  | `(slotted_lvl|$n:num)                   => return n.getNat.toLevel
  | `(slotted_lvl|(uvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
  | `(slotted_lvl|(param $n))               => return .param (.mkStr1 n.getString)
  | `(slotted_lvl|(succ $lvl))              => return .succ (← parseLevel lvl)
  | `(slotted_lvl|(max $lvl₁ $lvl₂))        => return .max (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(slotted_lvl|(imax $lvl₁ $lvl₂))       => return .imax (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(slotted_lvl|(Rewrite$dir $src $body)) => parseRw dir src body
  | _                                       => unreachable!
where
  parseRw (dir : TSyntax `rw_dir) (src : TSyntax `rw_src) (body : TSyntax `slotted_lvl) :
      ParseStepM Level := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir  := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := none : Rewrite.Info }
    parseLevel body

private abbrev ParseStepResult := Except ParseError <| Expression × (Option Rewrite.Info)

private partial def parseExpr (stx : TSyntax `slotted_expr) : ParseStepResult :=
  let (e, info?) := go .root stx |>.run none
  return (← e, info?)
where
  go (pos : SubExpr.Pos) : (TSyntax `slotted_expr) → ParseStepM Expression
    | `(slotted_expr|(bvar $s))                => return .bvar (parseSlot s)
    | `(slotted_expr|(fvar $id))               => return .fvar (.fromUniqueIdx id.getNat)
    | `(slotted_expr|(mvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
    | `(slotted_expr|(sort $lvl))              => return .sort (← parseLevel lvl)
    | `(slotted_expr|(const $name $lvls*))     => return .const name.getString.toName (← lvls.mapM parseLevel).toList
    | `(slotted_expr|(app $fn $arg))           => return .app (← go pos.pushAppFn fn) (← go pos.pushAppArg arg)
    | `(slotted_expr|(λ $var $ty $body))       => return .lam (parseSlot var) (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(slotted_expr|(∀ $var $ty $body))       => return .forall (parseSlot var) (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(slotted_expr|(lit $l))                 => return .lit (parseLit l)
    | `(slotted_expr|(proof $p))               => return .proof (← parseProof p pos)
    | `(slotted_expr|(↦ $var $to $e))          => return .subst (parseSlot var) (← go pos to) (← go pos e)
    | `(slotted_expr|_)                        => return .unknown
    | `(slotted_expr|(Rewrite$dir $src $body)) => parseRw dir src body pos
    | _                                        => unreachable!

  parseProof (p : TSyntax `slotted_expr) (pos : SubExpr.Pos) : ParseStepM Expression := do
    -- If `p` did not contain a rewrite, all is well and we return `e`. Otherwise, obtain the
    -- `rwInfo` and make sure it is a defeq rewrite. If not, we have a non-defeq type-level rewrite,
    -- which we cannot handle, yet.
    let rwIsOutsideProof := (← get).isSome
    let e ← go pos p
    if let some rwInfo ← get then
      unless rwIsOutsideProof || rwInfo.src.isDefEq do throw .nonDefeqProofRw
    return e

  parseRw (dir : TSyntax `rw_dir) (src : TSyntax `rw_src) (body : TSyntax `slotted_expr)
      (pos : SubExpr.Pos) : ParseStepM Expression := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir  := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := pos : Rewrite.Info }
    go pos body

end Slotted

def parseSlottedExpl : (TSyntax `slotted_expl) → MetaM Explanation
  | `(slotted_expl|$steps:slotted_expr*) => do
    let some start := steps[0]? | throwError ParseError.noSteps
    let .ok (start, none) := Slotted.parseExpr start | throwError ParseError.startContainsRw
    let mut tl : Array Step := #[]
    for step in steps[1:] do
      match Slotted.parseExpr step with
      | .error e             => throwError e
      | .ok (_, none)        => throwError ParseError.missingRw
      | .ok (dst, some info) => tl := tl.push { info with dst := ← dst.toExpr }
    return { start := ← start.toExpr, steps := tl }
  | _ => unreachable!
