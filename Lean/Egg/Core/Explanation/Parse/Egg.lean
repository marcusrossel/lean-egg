import Egg.Core.Explanation.Parse.Shared
import Lean
open Lean Meta

namespace Egg.Explanation

private inductive Expression where
  | bvar   (idx : Nat)
  | fvar   (id : FVarId)
  | mvar   (id : MVarId)
  | sort   (lvl : Level)
  | const  (name : Name) (lvls : List Level)
  | app    (fn arg : Expression)
  | lam    (ty body : Expression)
  | forall (ty body : Expression)
  | lit    (l : Literal)
  | eq     (lhs rhs : Expression)
  | proof  (prop : Expression)
  | inst   (cls : Expression)
  | subst  (idx : Nat) (to e : Expression)
  | shift  (offset : Int) (cutoff : Nat) (e : Expression)
  | unknown
deriving Inhabited, Repr

private def Expression.pp (levels := false) :  Expression → String
  | bvar idx => toString idx
  | fvar id => toString id.name
  | mvar id => s!"?{toString id.name}"
  | sort lvl => if levels then s!"Sort.\{{toString lvl}}" else "Sort"
  | const name lvls => if levels then s!"{name}\{{",".intercalate <| lvls.map toString}}" else toString name
  | app fn arg => s!"({Expression.pp (levels:=levels) fn} {Expression.pp (levels:=levels) arg})"
  | lam _ body => s!"(λ.{Expression.pp (levels:=levels) body})"
  | «forall»  _ body => s!"(λ.{Expression.pp (levels:=levels) body})"
  | lit l => s!"{repr l}"
  | eq lhs rhs => s!"{Expression.pp (levels:=levels) lhs} = {Expression.pp (levels:=levels) rhs}"
  | proof _ => "⋯"
  | inst cls => s!"inst{Expression.pp (levels:=levels) cls}"
  | subst idx to e => s!"(subst {idx} {Expression.pp (levels:=levels) to} {Expression.pp (levels:=levels) e})"
  | shift offset cutoff e => s!"(shift {offset} {cutoff} {Expression.pp (levels:=levels) e}"
  | unknown => "???"

-- If `synthesize` is true, we try to fill type class instance holes immediately by synthesis.
private def Expression.toExpr (e : Expression) (synthesize := false) : MetaM Expr := do
  go e
where
  go : Expression → MetaM Expr
    | bvar idx        => return .bvar idx
    | fvar id         => return .fvar id
    | mvar id         => return .mvar id
    | sort lvl        => return .sort lvl
    | const name lvls => return .const name lvls
    | app fn arg      => return .app (← go fn) (← go arg)
    | lam ty body     => return .lam .anonymous (← go ty) (← go body) .default
    | .forall ty body => return .forallE .anonymous (← go ty) (← go body) .default
    | lit l           => return .lit l
    | eq lhs rhs      => do mkEquiv (← go lhs) (← go rhs)
    | proof prop      => do mkFreshExprMVar (← go prop)
    | inst cls        => do mkFreshExprMVar (← go cls)
    | subst idx to e  => return applySubst idx (← go to) (← go e)
    | shift off cut e => return applyShift off cut (← go e)
    | unknown         => mkFreshExprMVar none
  mkEquiv (lhs rhs : Expr) : MetaM Expr := do
    -- We assume that `lhs` and `rhs` have the same type.
    if ← (return !lhs.hasLooseBVars) <&&> (return (← inferType lhs).isProp) then
      return mkApp2 (.const ``Iff []) lhs rhs
    else
      -- We can't just use `mkEq` because `lhs` and `rhs` might contains bvars.
      return mkApp3 (.const ``Eq [← mkFreshLevelMVar]) (← mkFreshExprMVar none) lhs rhs
  mkInst (cls : Expr) : MetaM Expr := do
    if synthesize then
      if let some i ← Meta.synthInstance? cls then return i
    mkFreshExprMVar cls
  applySubst (idx : Nat) (to : Expr) : Expr → Expr
    | .bvar i          => if i = idx then to else .bvar i
    | .app fn arg      => .app (applySubst idx to fn) (applySubst idx to arg)
    -- We don't shift `to` here because that's already handled in the egg backend. That is, the
    -- given `Expression` should contain the required shifts explicitly.
    | .lam n d b i     => .lam n (applySubst idx to d) (applySubst (idx + 1) to b) i
    | .forallE n d b i => .forallE n (applySubst idx to d) (applySubst (idx + 1) to b) i
    | e                => e
  applyShift (off : Int) (cut : Nat) : Expr → Expr
    | .bvar idx        => if idx < cut then .bvar idx else .bvar (idx + off).toNat
    | .app fn arg      => .app (applyShift off cut fn) (applyShift off cut arg)
    | .lam n d b i     => .lam n (applyShift off cut d) (applyShift off (cut + 1) b) i
    | .forallE n d b i => .forallE n (applyShift off cut d) (applyShift off (cut + 1) b) i
    | e                => e

declare_syntax_cat egg_lvl
declare_syntax_cat egg_expr
declare_syntax_cat egg_expl

syntax num                                           : egg_lvl
syntax "(" &"uvar" num ")"                           : egg_lvl
syntax "(" &"param" ident ")"                        : egg_lvl
syntax "(" &"succ" egg_lvl ")"                       : egg_lvl
syntax "(" &"max" egg_lvl egg_lvl ")"                : egg_lvl
syntax "(" &"imax" egg_lvl egg_lvl ")"               : egg_lvl
syntax "(" &"Rewrite" noWs rw_dir rw_src egg_lvl ")" : egg_lvl

syntax "(" &"bvar" num ")"                            : egg_expr
syntax "(" &"fvar" num ")"                            : egg_expr
syntax "(" &"mvar" num ")"                            : egg_expr
syntax "(" &"sort" egg_lvl ")"                        : egg_expr
syntax "(" &"const" ident egg_lvl* ")"                : egg_expr
syntax "(" &"app" egg_expr egg_expr ")"               : egg_expr
syntax "(" &"λ" egg_expr egg_expr ")"                 : egg_expr
syntax "(" &"∀" egg_expr egg_expr ")"                 : egg_expr
syntax "(" &"lit" lit ")"                             : egg_expr
syntax "(" &"=" egg_expr egg_expr ")"                 : egg_expr
syntax "(" &"proof" egg_expr ")"                      : egg_expr
syntax "(" &"inst" egg_expr ")"                       : egg_expr
syntax "(" &"↦" num egg_expr egg_expr ")"             : egg_expr
syntax "(" &"↑" shift_offset num egg_expr ")"         : egg_expr
syntax "(" "◇" shape egg_expr ")"                     : egg_expr
syntax &"_"                                           : egg_expr
syntax "(" &"Rewrite" noWs rw_dir rw_src egg_expr ")" : egg_expr

syntax egg_expr+ : egg_expl

private partial def parseLevel : (TSyntax `egg_lvl) → ParseStepM Level
  | `(egg_lvl|$n:num)                   => return n.getNat.toLevel
  | `(egg_lvl|(uvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
  | `(egg_lvl|(param $n))               => return .param n.getId
  | `(egg_lvl|(succ $lvl))              => return .succ (← parseLevel lvl)
  | `(egg_lvl|(max $lvl₁ $lvl₂))        => return .max (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(egg_lvl|(imax $lvl₁ $lvl₂))       => return .imax (← parseLevel lvl₁) (← parseLevel lvl₂)
  | `(egg_lvl|(Rewrite$dir $src $body)) => parseRw dir src body
  | _                                   => unreachable!
where
  parseRw (dir : TSyntax `rw_dir) (src : TSyntax `rw_src) (body : TSyntax `egg_lvl) :
      ParseStepM Level := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir  := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := none : Rewrite.Info }
    parseLevel body

private abbrev ParseStepResult := Except ParseError <| Expression × (Option Rewrite.Info)

partial def parseExpr (stx : TSyntax `egg_expr) : ParseStepResult :=
  let (e, info?) := go .root stx |>.run none
  return (← e, info?)
where
  go (pos : SubExpr.Pos) : (TSyntax `egg_expr) → ParseStepM Expression
    | `(egg_expr|(bvar $idx))              => return .bvar idx.getNat
    | `(egg_expr|(fvar $id))               => return .fvar (.fromUniqueIdx id.getNat)
    | `(egg_expr|(mvar $id))               => return .mvar (.fromUniqueIdx id.getNat)
    | `(egg_expr|(sort $lvl))              => return .sort (← parseLevel lvl)
    | `(egg_expr|(const $name $lvls*))     => return .const name.getId (← lvls.mapM parseLevel).toList
    | `(egg_expr|(app $fn $arg))           => return .app (← go pos.pushAppFn fn) (← go pos.pushAppArg arg)
    | `(egg_expr|(λ $ty $body))            => return .lam (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(egg_expr|(∀ $ty $body))            => return .forall (← go pos.pushBindingDomain ty) (← go pos.pushBindingBody body)
    | `(egg_expr|(lit $l))                 => return .lit (parseLit l)
    | `(egg_expr|(= $lhs $rhs))            => return .eq (← go (eqLhsPos pos) lhs) (← go (eqRhsPos pos) rhs)
    | `(egg_expr|(proof $p))               => return .proof (← parseTypeOfErased p pos)
    | `(egg_expr|(inst $c))                => return .inst (← parseTypeOfErased c pos)
    | `(egg_expr|(↦ $idx $to $e))          => return .subst idx.getNat (← go pos to) (← go pos e)
    | `(egg_expr|(↑ $off $cut $e))         => return .shift (parseShiftOffset off) cut.getNat (← go pos e)
    | `(egg_expr|(◇ $_ $e))                => go pos e
    | `(egg_expr|_)                        => return .unknown
    | `(egg_expr|(Rewrite$dir $src $body)) => parseRw dir src body pos
    | _                                    => unreachable!

  eqLhsPos (init : SubExpr.Pos) : SubExpr.Pos := init.pushAppFn.pushAppArg
  eqRhsPos (init : SubExpr.Pos) : SubExpr.Pos := init.pushAppArg

  parseTypeOfErased (t : TSyntax `egg_expr) (pos : SubExpr.Pos) : ParseStepM Expression := do
    -- If `t` did not contain a rewrite, all is well and we return `e`. Otherwise, obtain the
    -- `rwInfo` and make sure it is a defeq rewrite. If not, we have a non-defeq type-level rewrite,
    -- which we cannot handle, yet.
    let rwIsOutsideType := (← get).isSome
    let e ← go pos t
    if let some rwInfo ← get then
      unless rwIsOutsideType || rwInfo.id.src.isDefEq do throw .nonDefeqTypeRw
    return e

  parseRw (dir : TSyntax `rw_dir) (src : TSyntax `rw_src) (body : TSyntax `egg_expr)
      (pos : SubExpr.Pos) : ParseStepM Expression := do
    unless (← get).isNone do throw .multipleRws
    let info := parseRwSrc src
    let dir  := info.dir.merge (parseRwDir dir)
    set <| some { info with dir, pos? := pos : Rewrite.Info }
    go pos body

def parseEggExpl : (TSyntax `egg_expl) → MetaM Explanation.Steps
  | `(egg_expl|$steps:egg_expr*) => do
    let some start := steps[0]? | throwError ParseError.noSteps
    let .ok (start, none) := parseExpr start | throwError ParseError.startContainsRw
    let mut tl : Array Step := #[]
    for step in steps[1:] do
      match parseExpr step with
      | .error e             => throwError e
      | .ok (_, none)        => throwError ParseError.missingRw
      | .ok (dst, some info) => tl := tl.push { info with dst := ← dst.toExpr }
    return { start := ← start.toExpr, steps := tl }
  | _ => unreachable!
