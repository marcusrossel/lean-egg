import Egg.Core.Rewrites
import Lean

open Lean Meta Elab Tactic

namespace Egg

declare_syntax_cat egg_rws_list
syntax ("[" term,* "]")? : egg_rws_list
syntax "[" "*" "]" : egg_rws_list

declare_syntax_cat egg_rws
syntax (egg_rws_list)? : egg_rws

namespace Rewrite.Candidates

-- Note: We must use `Tactic.elabTerm`, not `Term.elabTerm`. Otherwise elaborating `‹...›` doesn't
--       work correctly. Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Elaborate.20.E2.80.B9.2E.2E.2E.E2.80.BA
--
-- Note: When a given rewrite is not a proof, we assume it's a function and try to get its equations
--       instead.
partial def explicit (rws : Array Term) : TacticM Rewrite.Candidates := do
  go none rws
where
  go (eqnIdx? : Option Nat) (rws : Array Term) : TacticM Rewrite.Candidates := do
    let mut result : Rewrite.Candidates := #[]
    for idx in [:rws.size], rw in rws do
      let e ← Tactic.elabTerm rw none
      let src := .explicit idx eqnIdx? rw
      if let some rw ← Rewrite.Candidate.from? (← inferType e) src then
        result := result.push rw
      else
        let some eqns ← equations? rw
          | throwErrorAt rw "'egg' tactic requires arguments to be equalities, equivalences or (non-propositional) definitions"
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
def star : MetaM Rewrite.Candidates := do
  let mut result : Rewrite.Candidates := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isAuxDecl then continue
    if let some rw ← Rewrite.Candidate.from? decl.type (.star decl.fvarId) then
      result := result.push rw
  return result

def parse : (TSyntax `egg_rws) → TacticM Rewrite.Candidates
  | `(egg_rws|)         => return {}
  | `(egg_rws|[*])      => star
  | `(egg_rws|[$rws,*]) => explicit rws
  | _                   => throwUnsupportedSyntax
