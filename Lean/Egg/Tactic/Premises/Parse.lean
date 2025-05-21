import Egg.Core.Rewrite.Basic
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_premise
syntax "*"  : egg_premise
syntax term : egg_premise

declare_syntax_cat egg_premise_list
syntax "[" egg_premise,* "]" : egg_premise_list

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

private abbrev Premise.Mk  (α) := Expr → Expr → Source → TacticM (Array α)
private abbrev Premise.Mk?     := Premise.Mk

private def Premise.Mk.rewrites
    (genGroundEqs : Bool) (stx : Syntax) (cfg : Config.Normalization) : Premise.Mk Rewrite :=
  fun proof type src => do
    let mut rws := #[]
    let some rw ← Rewrite.from? proof type src cfg
      | throwErrorAt stx "egg requires premises to be (proofs of) propositions or (non-propositional) definitions"
    rws := rws.push rw
    if genGroundEqs then
      if let some eq ← Rewrite.mkGroundEq? proof type (.ground src) cfg then
      rws := rws.push eq
    return rws

private def Premise.Mk?.rewrites
    (genGroundEqs : Bool) (cfg : Config.Normalization) : Premise.Mk? Rewrite :=
  fun proof type src => do
    let mut rws := #[]
    if let some rw ← Rewrite.from? proof type src cfg then rws := rws.push rw
    if genGroundEqs then
      if let some eq ← Rewrite.mkGroundEq? proof type (.ground src) cfg then rws := rws.push eq
    return rws

private def Premises.explicit
    (prem : Term) (idx : Idx) (mk : Premise.Mk α) (mkSrc : Idx → Option Nat → Source) :
    TacticM <| WithSyntax (Array α) := do
  match ← Premise.Raw.elab prem with
  | .single e type? =>
    let prems ← make e type? none
    return { elems := prems, stxs := ⟨List.replicate prems.size prem⟩ }
  | .eqns eqs =>
    let mut result : WithSyntax (Array α) := ∅
    for (val, ty) in eqs, eqnIdx in [:eqs.size] do
      for p in ← make val ty eqnIdx do
        result := result.push p prem
    return result
where
  make (e : Expr) (ty? : Option Expr) (eqnIdx? : Option Nat) : TacticM (Array α) := do
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
    for prem in ← mk decl.toExpr decl.type src do
      result := result.push prem stx
  return result

structure Premises where
  rws : WithSyntax Rewrites := ∅

def Premises.elab
    (cfg : Config.Normalization) (genGroundEqs : Bool) : (TSyntax `egg_premises) → TacticM Premises
  | `(egg_premises|) => return {}
  | `(egg_premises|[$rws,*]) =>
    let mk  := (Premise.Mk.rewrites genGroundEqs · cfg)
    let mk? := Premise.Mk?.rewrites genGroundEqs cfg
    return { rws := ← go rws mk mk? .explicit .star }
  | _ => throwUnsupportedSyntax
where
  go {α} (prems : Array <| TSyntax `egg_premise) (mk : Syntax → Premise.Mk α) (mk? : Premise.Mk? α)
      (mkExplicitSrc : Nat → Option Nat → Source) (mkStarSrc : FVarId → Source) :
      TacticM <| WithSyntax (Array α) := do
    let mut result : WithSyntax (Array α) := {}
    let mut noStar := true
    for prem in prems, idx in [:prems.size] do
      match prem with
      | `(egg_premise|$prem:term) =>
        result := result ++ (← explicit prem idx (mk prem) mkExplicitSrc)
      | `(egg_premise|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*'"
        noStar := false
        result := result ++ (← star tk mk? mkStarSrc)
      | _ => throwUnsupportedSyntax
    return result

def Premises.elabTagged (prems : Array Name) (cfg : Config.Normalization) : TacticM Rewrites := do
  let mut rws : Rewrites := #[]
  for prem in prems do
    rws := rws ++ (← taggedRw prem)
  return rws
where
  taggedRw (prem : Name) : TacticM Rewrites := do
    let ident := mkIdent prem
    let mk := Premise.Mk.rewrites (genGroundEqs := false) ident cfg
    let rws ← Premises.explicit ident prem mk .tagged
    return rws.elems
