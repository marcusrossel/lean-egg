import Egg.Core.Premise.Rewrites
import Egg.Core.Premise.Facts
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

inductive Premise.Raw where
  | single (expr : Expr) (type? : Option Expr := none)
  | eqns (exprs : Array (Expr × Expr))

-- We don't just elaborate premises directly as:
-- (1) this can cause problems for global constants with typeclass arguments, as Lean sometimes
--     tries to synthesize the arguments and fails if it can't (instead of inserting mvars).
-- (2) global constants which are definitions with equations (cf. `getEqnsFor?`) are supposed to
--     be replaced by their defining equations.
partial def Premise.Raw.elab (prem : Term) : TacticM Premise.Raw := do
  if let some hyp ← optional (getFVarId prem) then
    -- `prem` is a local declaration.
    let decl ← hyp.getDecl
    if decl.isImplementationDetail || decl.isAuxDecl then
      throwErrorAt prem "egg does not support using auxiliary declarations"
    else
      return .single (.fvar hyp) (← hyp.getType)
  else if let some const ← optional (realizeGlobalConstNoOverloadWithInfo prem) then
    if let some eqs ← getEqnsFor? const then
      -- `prem` is a global definition.
      return .eqns <| ← eqs.mapM (elabGlobalConstNoEqns ·)
    else
      -- `prem` is an global constant which is not a definition with equations.
      let (val, type) ← elabGlobalConstNoEqns const
      return .single val type
  else
    -- `prem` is an invalid identifier or a term which is not an identifier.
    -- We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
    -- work correctly. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
    return .single (← Tactic.elabTerm prem none)
where
  elabGlobalConstNoEqns (const : Name) : MetaM (Expr × Expr) := do
    let val ← mkConstWithFreshMVarLevels const
    let type ← inferType val
    return (val, type)

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

private def Premise.Mk.fact (stx : Syntax) : Premise.Mk Fact :=
  fun proof type src => do
    (← Fact.from? proof type src).getDM <|
      throwErrorAt stx m!"egg requires facts to be proofs or type class instances"

private def Premise.Mk?.fact : Premise.Mk? Fact :=
  (Fact.from? · · ·)

private def Premises.explicit
    (prem : Term) (idx : Nat) (mk : Premise.Mk α) (mkSrc : Nat → Option Nat → Source) :
    TacticM <| WithSyntax (Array α) := do
  match ← Premise.Raw.elab prem with
  | .single e type? => return { elems := #[(← make e type? none)], stxs := #[prem] }
  | .eqns eqs =>
    let mut result : WithSyntax (Array α) := ∅
    for (val, ty) in eqs, eqnIdx in [:eqs.size] do
      result := result.push (← make val ty eqnIdx) prem
    return result
where
  make (e : Expr) (ty? : Option Expr) (eqnIdx? : Option Nat) : TacticM α := do
    let src := mkSrc idx eqnIdx?
    let ty := ty?.getD (← inferType e)
    mk e ty src

-- Note: This function is expected to be called with the lctx which contains the desired premises.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
private def Premises.star (stx : Syntax) (mk : Premise.Mk? α) (mkSrc : FVarId → Source) :
    TacticM <| WithSyntax (Array α) := do
  let mut result : WithSyntax (Array α) := ∅
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let src := mkSrc decl.fvarId
    if let some prem ← mk decl.toExpr decl.type src then
      result := result.push prem stx
  return result

structure Premises where
  rws   : WithSyntax Rewrites := ∅
  facts : WithSyntax Facts    := ∅

def Premises.elab (cfg : Rewrite.Config) : (TSyntax `egg_premises) → TacticM Premises
  | `(egg_premises|) => return {}
  | `(egg_premises|[$rws,* $[; $facts?,*]?]) => do
    let mut result := {
      rws := ← go rws (Premise.Mk.rewrite · cfg) (Premise.Mk?.rewrite cfg) .explicit .star
    }
    if let some facts := facts? then
      let mkExplicitSrc idx _ := .fact (.explicit idx)
      let mkStarSrc id := .fact (.star id)
      result := { result with
        facts := ← go facts Premise.Mk.fact Premise.Mk?.fact mkExplicitSrc mkStarSrc
      }
    return result
  | _ => throwUnsupportedSyntax
where
  go {α} (prems : Array <| TSyntax `egg_premise) (mk : Syntax → Premise.Mk α) (mk? : Premise.Mk? α)
      (mkExplicitSrc : Nat → Option Nat → Source) (mkStarSrc : FVarId → Source) :
      TacticM <| WithSyntax (Array α) := do
    let mut result : WithSyntax (Array α) := {}
    let mut noStar := true
    for prem in prems, idx in [:prems.size] do
      match prem with
      | `(egg_premise|$prem:term) => result := result ++ (← explicit prem idx (mk prem) mkExplicitSrc)
      | `(egg_premise|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*'"
        noStar := false
        result := result ++ (← star tk mk? mkStarSrc)
      | _ => throwUnsupportedSyntax
    return result

def Premises.elabTagged (prems : Array Name) (cfg : Rewrite.Config) : TacticM Rewrites := do
  let mut rws : Rewrites := #[]
  for prem in prems, idx in [:prems.size] do
    rws := rws ++ (← taggedRw prem idx)
  return rws
where
  taggedRw (prem : Name) (idx : Nat) : TacticM Rewrites := do
    let ident := mkIdent prem
    let mk := Premise.Mk.rewrite ident cfg
    let rws ← Premises.explicit ident idx mk .tagged
    return rws.elems
