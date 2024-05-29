import Egg.Core.Premise.Rewrites
import Egg.Core.Premise.Facts
import Egg.Tactic.Premises.Validate
import Egg.Tactic.Tags
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_premise
syntax "*"  : egg_premise
syntax term : egg_premise

declare_syntax_cat egg_premise_list
syntax "[" egg_premise,* ("; " egg_premise,+)? "]" : egg_premise_list

declare_syntax_cat egg_premises
syntax (egg_premise_list)? : egg_premises

structure WithSyntax (α) where
  elems : α
  stxs  : Array Syntax := #[]

private instance : EmptyCollection <| WithSyntax (Array α) where
  emptyCollection := {
    elems := #[]
    stxs  := #[]
  }

private def WithSyntax.push (ws : WithSyntax (Array α)) (elem : α) (stx : Syntax) : WithSyntax (Array α) where
  elems := ws.elems.push elem
  stxs  := ws.stxs.push stx

private instance : Append <| WithSyntax (Array α) where
  append ws₁ ws₂ := {
    elems := ws₁.elems ++ ws₂.elems
    stxs  := ws₁.stxs ++ ws₂.stxs
  }

private abbrev Premise.Mk  (α) := Expr → Expr → Source → TacticM α
private abbrev Premise.Mk? (α) := Expr → Expr → Source → TacticM (Option α)

private def Premise.Mk.rewrite (stx : Syntax) (cfg : Rewrite.Config) : Premise.Mk Rewrite :=
  fun proof type src => do
    (← Rewrite.from? proof type src cfg).getDM <|
      throwErrorAt stx "egg requires rewrites to be equalities, equivalences or (non-propositional) definitions"

private def Premise.Mk?.rewrite (cfg : Rewrite.Config) : Premise.Mk? Rewrite :=
  (Rewrite.from? · · · cfg)

private def Premise.Mk.fact : Premise.Mk Fact :=
  fun proof type src => Fact.from proof type (.fact src)

private def Premise.Mk?.fact : Premise.Mk? Fact :=
  fun proof type src => Fact.from proof type (.fact src)

private def Premises.explicit
    (prem : Term) (idx : Nat) (mk : Premise.Mk α) (mkSrc : Nat → Option Nat → Source := .explicit) :
    TacticM <| WithSyntax (Array α) := do
  match ← Premise.Raw.elab prem with
  | .single e type? => return { elems := #[(← make e type? none)], stxs := #[prem] }
  | .eqns eqs =>
    let mut result : WithSyntax (Array α) := ∅
    for eqn in eqs, eqnIdx in [:eqs.size] do
      result := result.push (← make eqn none eqnIdx) prem
    return result
where
  make (e : Expr) (ty? : Option Expr) (eqnIdx? : Option Nat) : TacticM α := do
    let src := mkSrc idx eqnIdx?
    let ty := ty?.getD (← inferType e)
    mk e ty src

private def Premises.taggedRw (prem : Name) (idx : Nat) (cfg : Rewrite.Config) : TacticM Rewrites := do
  let ident := mkIdent prem
  let mk := Premise.Mk.rewrite ident cfg
  let rws ← Premises.explicit ident idx mk .tagged
  return rws.elems

private def Premises.elabTagged (prems : Array Name) (cfg : Rewrite.Config) : TacticM Rewrites := do
  let mut rws : Rewrites := #[]
  for prem in prems, idx in [:prems.size] do
    rws := rws ++ (← taggedRw prem idx cfg)
  return rws

def Premises.buildTagged (cfg : Config) (amb : MVars.Ambient ): TacticM Rewrites :=
  match cfg.tagged? with
    | none => return {}
    | some _ => do -- This should later use this `Name` to find the proper extension
      let prems := eggXtension.getState (← getEnv)
      elabTagged prems { norm? := cfg, amb}

-- Note: This function is expected to be called with the lctx which contains the desired premises.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
private def Premises.star (stx : Syntax) (mk : Premise.Mk? α) : TacticM <| WithSyntax (Array α) := do
  let mut result : WithSyntax (Array α) := ∅
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let src := Source.star decl.fvarId
    if let some prem ← mk decl.toExpr decl.type src then
      result := result.push prem stx
  return result

structure Premises where
  rws   : WithSyntax Rewrites := ∅
  facts : WithSyntax Facts    := ∅

def Premises.elab (cfg : Rewrite.Config) : (TSyntax `egg_premises) → TacticM Premises
  | `(egg_premises|) => return {}
  | `(egg_premises|[$rws,* $[; $facts?,*]?]) => do
    let mut result := { rws := ← go rws (Premise.Mk.rewrite · cfg) (Premise.Mk?.rewrite cfg) }
    if let some facts := facts? then
      result := { result with facts := ← go facts (fun _ => Premise.Mk.fact) Premise.Mk?.fact }
    return result
  | _ => throwUnsupportedSyntax
where
  go {α} (prems : Array <| TSyntax `egg_premise) (mk : Syntax → Premise.Mk α) (mk? : Premise.Mk? α) :
      TacticM <| WithSyntax (Array α) := do
    let mut result : WithSyntax (Array α) := {}
    let mut noStar := true
    for prem in prems, idx in [:prems.size] do
      match prem with
      | `(egg_premise|$prem:term) => result := result ++ (← explicit prem idx <| mk prem)
      | `(egg_premise|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*'"
        noStar := false
        result := result ++ (← star tk mk?)
      | _ => throwUnsupportedSyntax
    return result
