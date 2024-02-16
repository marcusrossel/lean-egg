import Egg.Core.Rewrites.Directions
import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta

namespace Egg.Rewrite

-- When constructed from a theorem `thm : ∀ xs, l ~ r`, the resulting rewrite has:
-- * `type := { lhs := l, rhs := r, rel := ~ }`
-- * `holes := xs`
-- * `proof := thm xs` - that is, the arguments are instantiated
--
-- Note: When constructing the valid directions of a rewrite, we check mvar inclusion for two
--       different domains: expressions and levels. We separately capture which directions are valid
--       for which domain. This is relevant when `Config.eraseConstLvls = true`.
structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof : Expr
  holes : Array MVarId
  src   : Source
  private validExprDirs : Directions
  private validLvlDirs  : Directions

-- TODO: The distinction between expr mvars and level mvars isn't sufficient. We actually need to
--       also distinguish between const level mvars and sort level mvars. The former become
--       irrelevant upon `Config.eraseConstLvls = true` while the latter don't.
--       To fix this, implement your own level mvar collection that distinguishes the two.
def validDirs (rw : Rewrite) (ignoreULvls : Bool) : Directions :=
  if ignoreULvls then rw.validExprDirs else rw.validExprDirs.meet rw.validLvlDirs

-- Returns the same rewrite but with all holes replaced by fresh mvars. This is used during proof
-- reconstruction, as rewrites may be used multiple times but instantiated differently. If we don't
-- use fresh mvars, the holes will already be assigned and assignment (via `isDefEq`) will fail.
def fresh (rw : Rewrite) : MetaM Rewrite := do
  let mut freshMVars : HashMap MVarId Expr := ∅
  let mut holes : Array MVarId := .mkEmpty rw.holes.size
  for hole in rw.holes do
    let fresh ← mkFreshExprMVar (← hole.getType)
    freshMVars := freshMVars.insert hole fresh
    holes := holes.push fresh.mvarId!
  let refreshMVars e := if e.isMVar then freshMVars.find? e.mvarId! else none
  let lhs   := rw.lhs.replace refreshMVars
  let rhs   := rw.rhs.replace refreshMVars
  let proof := rw.proof.replace refreshMVars
  return { rw with lhs, rhs, holes, proof }

-- Returns the same rewrite but with its type and proof potentially flipped to match the given
-- direction.
def forDir (rw : Rewrite) : Direction → MetaM Rewrite
  | .forward  => return rw
  | .backward => return { rw with lhs := rw.rhs, rhs := rw.lhs, proof := ← rw.rel.mkSymm rw.proof }

-- Note: We normalize the `lhs` and `rhs` of the rewrite.
--
-- Note: It isn't sufficient to take the `args` as `holes`, as implicit arguments will already be
--       instantiated as mvars during type inference. For example, the type of
--       `theorem t : ∀ {x}, x + 0 = 0 + x := Nat.add_comm _ _` will be directly inferred as
--       `?x + 0 = 0 + ?x`.
--
-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, cf.
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
--
-- TODO: We could make this more efficient by using the mvars collected in `dirs` to populate the
--      `holes`.
def from? (proof : Expr) (type : Expr) (src : Source) : MetaM (Option Rewrite) := do
  let mut (args, _, type) ← forallMetaTelescopeReducing (← instantiateMVars type)
  type ← normalize type
  let proof := mkAppN proof args
  let holes ← getMVars type
  let some cgr := Congr.from? type | return none
  let (validExprDirs, validLvlDirs) ← dirs cgr.lhs cgr.rhs
  return some { cgr with proof, holes, src, validExprDirs, validLvlDirs }
where
  dirs (lhs rhs : Expr) : MetaM (Directions × Directions) := do
    let exprDirs := Directions.satisfyingSuperset (← Meta.getMVars lhs) (← Meta.getMVars rhs)
    let lvlDirs  := Directions.satisfyingSuperset lhs.levelMVars.toArray rhs.levelMVars.toArray
    return (exprDirs, lvlDirs)

end Rewrite

abbrev Rewrites := Array Rewrite

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def Rewrites.find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
