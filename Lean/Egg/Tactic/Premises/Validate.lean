import Egg.Core.Premise.Rewrites

open Lean Meta Elab Tactic

inductive Premise.Raw where
  | single (expr : Expr) (type? : Option Expr := none)
  | eqns (exprs : Array Expr)

inductive Premise.RawRaw where
  | eqns (exprs : Array Name)
  | single (expr : Expr) (type? : Option Expr := none)
  | prem (prem : Term)


def Premise.Raw.validate (prem : Term) : MetaM Premise.RawRaw := do
  if let some const ← optional (resolveGlobalConstNoOverload prem) then
    if let some eqs ← getEqnsFor? const (nonRec := true) then
      -- `prem` is a global definition.
      return .eqns eqs
    else
      -- `prem` is an global constant which is not a definition with equations.
      let env ← getEnv
      let some info := env.find? const | throwErrorAt prem m!"unknown constant '{mkConst const}'"
      match info with
      | .defnInfo _ | .axiomInfo _ | .thmInfo _ | .opaqueInfo _ =>
        let lvlMVars ← List.replicateM info.numLevelParams mkFreshLevelMVar
        let val := if info.hasValue then info.instantiateValueLevelParams! lvlMVars else .const info.name lvlMVars
        let type := info.instantiateTypeLevelParams lvlMVars
        return .single val type
      | _ => throwErrorAt prem "egg requires arguments to be theorems, definitions or axioms"
  else
    -- `prem` is an invalid identifier or a term which is not an identifier.
    -- We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
    -- work correctly. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
    return .prem prem

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
  match (← validate prem) with
    | .eqns eqs => return .eqns <| ← eqs.mapM fun eqn => Tactic.elabTerm (mkIdent eqn) none
    | .single val type? => return .single val type?
    | .prem prem => return .single (← Tactic.elabTerm prem none)
