import Egg.Core.Rewrite.Rule

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_arg
syntax "*"  : egg_arg
syntax term : egg_arg

declare_syntax_cat egg_arg_list
syntax ("[" egg_arg,* "]")? : egg_arg_list

declare_syntax_cat egg_args
syntax (egg_arg_list)? : egg_args

inductive Argument.Raw where
  | single (expr : Expr) (type? : Option Expr := none)
  | eqns (exprs : Array (Expr × Expr))

-- We don't just elaborate arguments directly as:
-- (1) this can cause problems for global constants with typeclass arguments, as Lean sometimes
--     tries to synthesize the arguments and fails if it can't (instead of inserting mvars).
-- (2) global constants which are definitions with equations (cf. `getEqnsFor?`) are supposed to
--     be replaced by their defining equations.
partial def Argument.Raw.elab (arg : Term) : TacticM Argument.Raw := do
  if let some hyp ← optional (getFVarId arg) then
    -- `arg` is a local declaration.
    let decl ← hyp.getDecl
    if decl.isImplementationDetail || decl.isAuxDecl then
      throwErrorAt arg "egg does not support using auxiliary declarations"
    else
      return .single (.fvar hyp) (← hyp.getType)
  else if let some const ← optional (realizeGlobalConstNoOverloadWithInfo arg) then
    if let some eqs ← getEqnsFor? const then
      -- `arg` is a global definition.
      return .eqns <| ← eqs.mapM (elabGlobalConstNoEqns ·)
    else
      -- `arg` is an global constant which is not a definition with equations.
      let (val, type) ← elabGlobalConstNoEqns const
      return .single val type
  else
    -- `arg` is an invalid identifier or a term which is not an identifier.
    -- We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
    -- work correctly. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
    return .single (← Tactic.elabTerm arg none)
where
  elabGlobalConstNoEqns (const : Name) : MetaM (Expr × Expr) := do
    let val ← mkConstWithFreshMVarLevels const
    let type ← inferType val
    return (val, type)

namespace Rewrite.Rules

private def explicit
    (arg : Term) (idx : α) (mkSrc : α → Option Nat → Source) (groundEqs : Bool)
    (cfg : Config.Normalization) : TacticM Rules := do
  match ← Argument.Raw.elab arg with
  | .single e type? => make e type? none
  | .eqns eqs =>
    let mut result := ∅
    for (val, ty) in eqs, eqnIdx in [:eqs.size] do
      let new ← make val ty eqnIdx
      result := result ∪ new
    return result
where
  make (proof : Expr) (type? : Option Expr) (eqnIdx? : Option Nat) : TacticM Rules := do
    let src := mkSrc idx eqnIdx?
    let type := type?.getD (← inferType proof)
    let mut some rules ← (∅ : Rules).add? src proof type cfg .both arg
      | throwErrorAt arg "egg requires arguments to be (proofs of) propositions or (non-propositional) definitions"
    if groundEqs then
      if let some rules' ← rules.add? (.ground src) proof type cfg .ground arg then
        rules := rules'
    return rules

-- Note: This function is expected to be called with the lctx which contains the desired arguments.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
private def star (stx : Syntax) (groundEqs : Bool) (cfg : Config.Normalization) : TacticM Rules := do
  let mut result : Rules := ∅
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let src := .star decl.fvarId
    if let some result' ← result.add? src decl.toExpr decl.type cfg .both stx then
      result := result'
    if groundEqs then
      if let some result' ← result.add? (.ground src) decl.toExpr decl.type cfg .ground stx then
        result := result'
  return result

def «elab» (cfg : Config.Normalization) (groundEqs : Bool) : (TSyntax `egg_args) → TacticM Rules
  | `(egg_args|) => return {}
  | `(egg_args|[$args,*]) => do
    let mut result := ∅
    let mut noStar := true
    for arg in args.getElems, idx in [:args.getElems.size] do
      match arg with
      | `(egg_arg|$arg:term) =>
        let new ← explicit arg idx .explicit groundEqs cfg
        result := result ∪ new
      | `(egg_arg|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*'"
        noStar := false
        let new ← star tk groundEqs cfg
        result := result ∪ new
      | _ => throwUnsupportedSyntax
    return result
  | _ => throwUnsupportedSyntax

def elabTagged (args : Array Name) (cfg : Config.Normalization) : TacticM Rules := do
  let mut rules : Rules := ∅
  for arg in args do
    let new ← explicit (mkIdent arg) arg .tagged (groundEqs := false) cfg
    rules := rules ∪ new
  return rules

end Rewrite.Rules
