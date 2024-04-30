import Egg.Core.Premise.Basic
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_prems_arg
syntax "*"  : egg_prems_arg
syntax term : egg_prems_arg

declare_syntax_cat egg_prems_args
syntax "[" egg_prems_arg,* "]": egg_prems_args

declare_syntax_cat egg_prems
syntax (egg_prems_args)? : egg_prems

structure Premises where
  rws      : Rewrites     := #[]
  rwsStx   : Array Syntax := #[]
  facts    : Facts        := #[]
  factsStx : Array Syntax := #[]

namespace Premises

private def push (ps : Premises) (stx : Syntax) (p : Premise) : Premises := Id.run do
  let mut ps   := ps
  let mut isRw := false
  if let some rw := p.rw? then
    ps := { ps with rws := ps.rws.push rw, rwsStx := ps.rwsStx.push stx }
    isRw := true
  return { ps with facts := ps.facts.push p.fact, factsStx := ps.factsStx.push stx }

private def singleton (stx : Syntax)  (p : Premise) : Premises :=
  ({} : Premises).push stx p

private def append (ps₁ ps₂ : Premises) : Premises where
  rws      := ps₁.rws.append ps₂.rws
  rwsStx   := ps₁.rwsStx.append ps₂.rwsStx
  facts    := ps₁.facts.append ps₂.facts
  factsStx := ps₁.factsStx.append ps₂.factsStx

instance : Append Premises where
  append := append

-- Note: We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
--       work correctly. Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
partial def explicit (arg : Term) (argIdx : Nat) (norm : Config.Normalization) (amb : MVars.Ambient) :
    TacticM Premises := do
  match ← elabArg arg with
  | .inl (e, ty?) => return Premises.singleton arg (← mkPremise e ty? none)
  | .inr eqns =>
    let mut result : Premises := {}
    for eqn in eqns, eqnIdx in [:eqns.size] do
      let e ← Tactic.elabTerm eqn none
      result := result.push arg (← mkPremise e none eqnIdx)
    return result
  -- We don't just elaborate the `arg` directly as:
  -- (1) this can cause problems for global constants with typeclass arguments, as Lean sometimes
  --     tries to synthesize the arguments and fails if it can't (instead of inserting mvars).
  -- (2) global constants which are definitions with equations (cf. `getEqnsFor?`) are supposed to
  --     be replaced by their defining equations.
where
  -- Note: When we infer the type of `e` it might not have the syntactic form we expect. For
  --       example, if `e` is `congrArg (fun x => x + 1) (_ : a = b)` then its type will be inferred
  --       as `a + 1 = b + 1` instead of `(fun x => x + 1) a = (fun x => x + 1) b`.
  mkPremise (e : Expr) (ty? : Option Expr) (eqnIdx? : Option Nat) : TacticM Premise := do
    let src := .explicit argIdx eqnIdx?
    let ty := ty?.getD (← inferType e)
    Premise.from e ty src norm amb

  elabArg (arg : Term) : TacticM (Sum (Expr × Option Expr) (Array Ident)) := do
    if let some hyp ← optional (getFVarId arg) then
      -- `arg` is a local declaration.
      return .inl (.fvar hyp, ← hyp.getType)
    else if let some const ← optional (resolveGlobalConstNoOverload arg) then
      if let some eqns ← getEqnsFor? const (nonRec := true) then
        -- `arg` is a global definition.
        return .inr <| eqns.map (mkIdent ·)
      else
        -- `arg` is an global constant which is not a definition with equations.
        let env ← getEnv
        let some info := env.find? const | throwErrorAt arg m!"unknown constant '{mkConst const}'"
        unless info.hasValue do throwErrorAt arg "egg requires arguments to be theorems or definitions"
        let lvlMVars ← List.replicateM info.numLevelParams mkFreshLevelMVar
        let val := info.instantiateValueLevelParams! lvlMVars
        let type := info.instantiateTypeLevelParams lvlMVars
        return .inl (val, type)
    else
      -- `arg` is an invalid identifier or a term which is not an identifier.
      return .inl (← Tactic.elabTerm arg none, none)

-- Note: This function is expected to be called with the local context which contains the desired
--       rewrites.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
def star (stx : Syntax) (norm : Config.Normalization) (amb : MVars.Ambient) : MetaM Premises := do
  let mut result : Premises := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    let src := Source.star decl.fvarId
    result := result.push stx (← Premise.from decl.toExpr decl.type src norm amb)
  return result

def parse (norm : Config.Normalization) (amb : MVars.Ambient) : (TSyntax `egg_prems) → TacticM Premises
  | `(egg_prems|)          => return {}
  | `(egg_prems|[$args,*]) => do
    let mut result : Premises := {}
    let mut noStar := true
    for arg in args.getElems, idx in [:args.getElems.size] do
      match arg with
      | `(egg_prems_arg|$arg:term) => result := result ++ (← explicit arg idx norm amb)
      | `(egg_prems_arg|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*' in arguments to egg"
        noStar := false
        result := result ++ (← star tk norm amb)
      | _ => throwUnsupportedSyntax
    return result
  | _ => throwUnsupportedSyntax
