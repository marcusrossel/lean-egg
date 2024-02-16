import Egg.Core.Normalize
import Egg.Core.Congr
import Egg.Core.Source
import Egg.Lean
open Lean Meta Elab

namespace Egg.Rewrite

inductive Direction where
  | forward
  | backward
  deriving Inhabited

def Direction.merge : Direction → Direction → Direction
  | .forward, .forward  | .backward, .backward => .forward
  | .forward, .backward | .backward, .forward  => .backward

inductive Directions where
  | forward
  | backward
  | both

instance : ToString Directions where
  toString
    | .forward  => "forward"
    | .backward => "backward"
    | .both     => "both"

-- TODO: Is this the right approach, or would it be better the store the type as a `∀` expression?
--
-- When constructed from a theorem `thm : ∀ xs, l ~ r`, the resulting rewrite has:
-- * `type := { lhs := l, rhs := r, rel := ~ }`
-- * `holes := xs`
-- * `proof := thm xs` - that is, the arguments are instantiated
structure _root_.Egg.Rewrite extends Congr where
  private mk ::
  proof : Expr
  holes : Array MVarId
  src   : Source

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

-- The directions in which the given rewrite can be used. This depends on whether the mvars of the
-- respective sides are subsets of eachother.
def validDirs (rw : Rewrite) (ignoreULvls : Bool) : MetaM (Option Directions) := do
  let lhsM ← Meta.getMVars rw.lhs
  let rhsM ← Meta.getMVars rw.rhs
  let mut lSubR := lhsM.all rhsM.contains
  let mut rSubL := rhsM.all lhsM.contains
  if !ignoreULvls then
    let lhsL := rw.lhs.levelMVars
    let rhsL := rw.rhs.levelMVars
    lSubR := lSubR && lhsL.all rhsL.contains
    rSubL := rSubL && rhsL.all lhsL.contains
  match lSubR, rSubL with
  | false, false => return none
  | false, true  => return some .forward
  | true, false  => return some .backward
  | true, true   => return some .both

-- TODO: When we reduce the type, do we need to reduce the proof, too? Otherwise, might the proof
--       contain mvars which were removed when reducing the type, which then aren't assigned during
--       proof reconstruction?
--
-- Note: We normalize the `lhs` and `rhs` of the rewrite.
--
-- Note: It isn't sufficient to take the `args` as `holes`, as implicit arguments will already be
--       instantiated as mvars during type inference. For example, the type of
--       `theorem t : ∀ {x}, x + 0 = 0 + x := Nat.add_comm _ _` will be directly inferred as
--       `?x + 0 = 0 + ?x`.
--
-- Note: We must instantiate mvars of the rewrite's type. For an example that breaks otherwise, cf.
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Different.20elab.20results
def from? (proof : Expr) (type : Expr) (src : Source) : MetaM (Option Rewrite) := do
  let mut (args, _, type) ← forallMetaTelescopeReducing (← instantiateMVars type)
  type ← normalize type
  let proof := mkAppN proof args
  let holes ← getMVars type
  let some cgr := Congr.from? type | return none
  return some { cgr with proof, holes, src }

end Rewrite

abbrev Rewrites := Array Rewrite

namespace Rewrites

def validDirs! (rws : Rewrites) (ignoreULvls : Bool) : MetaM (Array Rewrite.Directions) :=
  rws.mapM fun rw => do
    let some dir ← rw.validDirs ignoreULvls | throwError m!"invalid rewrite {rw.src}: egg (currently) disallows rewrite rules with loose mvars or level mvars"
    return dir

-- TODO: This is unnecessarilly inefficient during proof reconstruction, so at some point we may
--       want to redefine `Rewrites` using a better suited data structure.
def find? (rws : Rewrites) (src : Source) : Option Rewrite :=
  Array.find? rws (·.src == src)
