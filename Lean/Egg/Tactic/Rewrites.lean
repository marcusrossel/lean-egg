import Egg.Core.Rewrites.Basic
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_rws_arg
syntax "*"  : egg_rws_arg
syntax term : egg_rws_arg

declare_syntax_cat egg_rws_args
syntax "[" egg_rws_arg,* "]": egg_rws_args

declare_syntax_cat egg_rws
syntax (egg_rws_args)? : egg_rws

namespace Rewrites

-- Note: We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
--       work correctly. Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
partial def explicit (arg : Term) (argIdx : Nat) (beta eta : Bool) : TacticM Rewrites := do
  match ← elabArg arg with
  | .inl (e, ty?) => return #[← mkRw e ty? none]
  | .inr eqns =>
    let mut result : Rewrites := #[]
    for eqn in eqns, eqnIdx in [:eqns.size] do
      let e ← Tactic.elabTerm eqn none
      result := result.push (← mkRw e none eqnIdx)
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
  mkRw (e : Expr) (ty? : Option Expr) (eqnIdx? : Option Nat) : TacticM Rewrite := do
    let src := .explicit argIdx eqnIdx?
    let ty := ty?.getD (← inferType e)
    let some rw ← Rewrite.from? e ty src beta eta
      | throwErrorAt arg "egg requires arguments to be equalities, equivalences or (non-propositional) definitions"
    return rw
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
def star (beta eta : Bool) : MetaM Rewrites := do
  let mut result : Rewrites := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    if let some rw ← Rewrite.from? decl.toExpr decl.type (.star decl.fvarId) beta eta
    then result := result.push rw
  return result

def parse (beta eta : Bool) : (TSyntax `egg_rws) → TacticM Rewrites
  | `(egg_rws|)          => return {}
  | `(egg_rws|[$args,*]) => do
    let mut result : Rewrites := #[]
    let mut noStar := true
    for arg in args.getElems, idx in [:args.getElems.size] do
      match arg with
      | `(egg_rws_arg|$arg:term) =>
        result := result ++ (← explicit arg idx beta eta)
      | `(egg_rws_arg|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*' in arguments to egg"
        noStar := false
        result := result ++ (← star beta eta)
      | _ =>
        throwUnsupportedSyntax
    return result
  | _ => throwUnsupportedSyntax
