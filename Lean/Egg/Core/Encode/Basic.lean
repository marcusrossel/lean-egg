import Egg.Lean
import Egg.Core.Normalize
import Egg.Core.Encode.EncodeM
import Lean
open Lean

namespace Egg

private def Expression.erased : Expression :=
  "_"

-- Note: The encoding of expression mvars and universe level mvars in rewrites relies on the fact
--       that their indices are also unique between eachother.

open EncodeM

private def encodeLevel : Level → EncodeM Expression
  | .zero       => return "0"
  | .succ l     => return s!"(succ {← encodeLevel l})"
  | .max l₁ l₂  => return s!"(max {← encodeLevel l₁} {← encodeLevel l₂})"
  | .imax l₁ l₂ => return s!"(imax {← encodeLevel l₁} {← encodeLevel l₂})"
  | .param name => return s!"(param {name})"
  | .mvar id    => do
    if (← isAmbientLvl id)
    then return s!"(uvar {id.uniqueIdx!})"
    else return s!"?{id.uniqueIdx!}"

structure EncodingCtx where
  cfg : Config.Encoding
  amb : MVars.Ambient

-- Note: This function expects its input expression to be normalized (cf. `Egg.normalize`).
partial def encode (e : Expr) (ctx : EncodingCtx) : MetaM Expression :=
  Prod.fst <$> (go e).run { config := ctx.cfg, amb := ctx.amb }
where
  go (e : Expr) : EncodeM Expression :=
    withCache e do
      if ← needsProofErasure e then
        let prop ← normalize (← Meta.inferType e) .noReduce
        return s!"(proof {← go prop})"
      else
        core e

  core : Expr → EncodeM Expression
    | .fvar id          => encodeFVar id
    | .mvar id          => encodeMVar id
    | .sort lvl         => return s!"(sort {← encodeLevel lvl})"
    | .const name lvls  => return s!"(const {name}{← encodeConstLvls lvls})"
    | .app fn arg       => return s!"(app {← go fn} {← go arg})"
    | .lam _ ty b _     => encodeLambda ty b
    | .forallE _ ty b _ => encodeForall ty b
    | .lit (.strVal l)  => return s!"(lit {Json.renderString l})"
    | .lit (.natVal l)  => return s!"(lit {l})"
    | .bvar _           => panic! "'Egg.encode.core' found loose bvar"
    | _                 => panic! "'Egg.encode.core' received non-normalized expression"

  encodeFVar (id : FVarId) : EncodeM Expression := do
    if let some bvarIdx ← bvarIdx? id
    then return s!"(bvar {bvarIdx})"
    else return s!"(fvar {id.uniqueIdx!})"

  encodeMVar (id : MVarId) : EncodeM Expression := do
    if (← isAmbientExpr id)
    then return s!"(mvar {id.uniqueIdx!})"
    else return s!"?{id.uniqueIdx!}"

  encodeConstLvls (lvls : List Level) : EncodeM Expression :=
    lvls.foldlM (init := "") (return s!"{·} {← encodeLevel ·}")

  encodeLambda (ty b : Expr) : EncodeM Expression := do
    -- It's critical that we encode `ty` outside of the `withInstantiatedBVar` block, as otherwise
    -- the bvars in `encTy` are incorrectly shifted by 1.
    let encTy ← go ty
    withInstantiatedBVar ty b fun body => return s!"(λ {encTy} {← go body})"

  encodeForall (ty b : Expr) : EncodeM Expression := do
    -- It's critical that we encode `ty` outside of the `withInstantiatedBVar` block, as otherwise
    -- the bvars in `encTy` are incorrectly shifted by 1.
    let encTy ← go ty
    withInstantiatedBVar ty b fun body => return s!"(∀ {encTy} {← go body})"
