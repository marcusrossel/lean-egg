import Egg.Core.Rewrites
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_rws_list
syntax ("[" term,* "]")? : egg_rws_list
syntax "[" "*" "]" : egg_rws_list

declare_syntax_cat egg_rws
syntax (egg_rws_list)? : egg_rws

namespace Rewrites

abbrev Parsed := Array (Rewrite × Syntax)

-- Note: We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
--       work correctly. Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
--
-- Note: When a given rewrite is not a proof, we assume it's a function and try to get its equations
--       instead.
partial def explicit (rws : Array Term) : TacticM Parsed := do
  go none rws
where
  go (eqnIdx? : Option Nat) (rws : Array Term) : TacticM Parsed := do
    let mut result : Parsed := #[]
    for idx in [:rws.size], stx in rws do
      let e ← Tactic.elabTerm stx none
      let src := .explicit idx eqnIdx?
      if let some rw ← Rewrite.from? (proof := e) (type := ← inferType e) src then
        result := result.push (rw, stx)
      else
        let some eqns ← equations? stx
          | throwErrorAt stx "'egg' tactic requires arguments to be equalities, equivalences or (non-propositional) definitions"
        let rws ← go idx eqns
        result := result ++ rws
    return result
  equations? (rw : Term) : MetaM <| Option (Array Term) := do
    let defName ← resolveGlobalConstNoOverload rw
    let some eqns ← getEqnsFor? defName (nonRec := true) | return none
    return eqns.map (mkIdent ·)

-- Note: This function is expected to be called with the local context which contains the desired
--       rewrites.
--
-- Note: We need to filter out auxiliary declaration and implementation details, as they are not
--       visible in the proof context and, for example, contain the declaration being defined itself
--       (to enable recursive calls). Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/local.20context.20without.20current.20decl
def star (stx : Syntax) : MetaM Parsed := do
  let mut result : Parsed := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    if let some rw ← Rewrite.from? (proof := decl.toExpr) (type := decl.type) (.star decl.fvarId)
    then result := result.push (rw, stx)
  return result

def parse : (TSyntax `egg_rws) → TacticM Parsed
  | `(egg_rws|)         => return {}
  | `(egg_rws|[*%$tk])  => star tk
  | `(egg_rws|[$rws,*]) => explicit rws
  | _                   => throwUnsupportedSyntax

def Parsed.withDirs (parsed : Parsed) (ignoreULvls : Bool) :
    MetaM (Rewrites × Array Rewrite.Directions) := do
  let mut rws := #[]
  let mut dirs := #[]
  for (rw, stx) in parsed do
    let some dir ← rw.validDirs ignoreULvls |
      throwErrorAt? stx "'egg' tactic (currently) disallows rewrite rules with loose mvars or level mvars"
    rws := rws.push rw
    dirs := dirs.push dir
  return (rws, dirs)
