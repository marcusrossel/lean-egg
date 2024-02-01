import Egg.Core.Rewrites
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

abbrev Parsed := Array (Rewrite × Syntax)

-- Note: We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
--       work correctly. Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
--
-- Note: When a given rewrite is not a proof, we assume it's a function and try to get its equations
--       instead.
--
-- Note: If `defIdx? = some i`, that means we're currently generating equations for the definition
--       with index `i`. Thus, the (leading) index of those equations should be `i`, while their
--       `eqnIdx?` should be the `idx` from the for-loop.
partial def explicit (arg : Term) (argIdx : Nat) (reduce : Bool) : TacticM Parsed := do
  go arg none
where
  go (arg : Term) (eqnIdx? : Option Nat) : TacticM Parsed := do
    let e ← Tactic.elabTerm arg none
    let src := .explicit argIdx eqnIdx?
    if let some rw ← Rewrite.from? e (← inferType e) src reduce then
      return #[(rw, arg)]
    else
      let some eqns ← equations? arg | throwErrorAt arg "egg requires arguments to be equalities, equivalences or (non-propositional) definitions"
      let mut result := #[]
      for eqn in eqns, eqnIdx in [:eqns.size] do
        result := result ++ (← go eqn eqnIdx)
      return result
  equations? (arg : Term) : MetaM <| Option (Array Term) := do
    let defName ← resolveGlobalConstNoOverload arg
    let some eqns ← getEqnsFor? defName (nonRec := true) | return none
    return eqns.map (mkIdent ·)

-- Note: This function is expected to be called with the local context which contains the desired
--       rewrites.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
def star (stx : Syntax) (reduce : Bool) : MetaM Parsed := do
  let mut result : Parsed := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    if let some rw ← Rewrite.from? decl.toExpr decl.type (.star decl.fvarId) reduce
    then result := result.push (rw, stx)
  return result

def parse (reduce : Bool) : (TSyntax `egg_rws) → TacticM Parsed
  | `(egg_rws|)          => return {}
  | `(egg_rws|[$args,*]) => do
    let mut result : Parsed := #[]
    let mut noStar := true
    for arg in args.getElems, idx in [:args.getElems.size] do
      match arg with
      | `(egg_rws_arg|$arg:term) =>
        result := result ++ (← explicit arg idx reduce)
      | `(egg_rws_arg|*%$tk) =>
        unless noStar do throwErrorAt tk "duplicate '*' in arguments to egg"
        noStar := false
        result := result ++ (← star tk reduce)
      | _ =>
        throwUnsupportedSyntax
    return result
  | _ => throwUnsupportedSyntax

def Parsed.withDirs (parsed : Parsed) (ignoreULvls : Bool) :
    MetaM (Rewrites × Array Rewrite.Directions) := do
  let mut rws := #[]
  let mut dirs := #[]
  for (rw, stx) in parsed do
    let some dir ← rw.validDirs ignoreULvls |
      throwErrorAt? stx "egg (currently) disallows rewrite rules with loose mvars or level mvars"
    rws := rws.push rw
    dirs := dirs.push dir
  return (rws, dirs)
