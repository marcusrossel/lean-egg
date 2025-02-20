import Egg.Lean
import Egg.Core.Normalize
import Egg.Core.Encode.EncodeM
import Egg.Core.Encode.Shapes
import Lean
open Lean

namespace Egg

open EncodeM

private def encodeLevel : Level → EncodeM Expression
  | .zero       => return "0"
  | .succ l     => return s!"(succ {← encodeLevel l})"
  | .max l₁ l₂  => return s!"(max {← encodeLevel l₁} {← encodeLevel l₂})"
  | .imax l₁ l₂ => return s!"(imax {← encodeLevel l₁} {← encodeLevel l₂})"
  | .param name => return s!"(param \"{name}\")"
  | .mvar id    => do
    if ← isLevelMVarAssignable id
    then return s!"?{id.uniqueIdx!}"
    else return s!"(uvar {id.uniqueIdx!})"

-- Note: This function expects its input expression to be normalized (cf. `Egg.normalize`).
partial def encode (e : Expr) (cfg : Config.Encoding) : MetaM Expression := do
  Prod.fst <$> (go e).run { config := cfg }
where
  go (e : Expr) : EncodeM Expression :=
    withCache e do
      let basic ←
        if ← needsProofErasure e then
          let prop ← normalize (← Meta.inferType e) .noReduce
          let enc ← withoutShapes do go prop
          pure s!"(proof {enc})"
        else if let some cls ← needsInstErasure? e then
          let cls ← normalize cls .noReduce
          let enc ← withoutShapes do go cls
          pure s!"(inst {enc})"
        else if let some (lhs, rhs) := e.eqOrIff? then
          pure s!"(= {← go lhs} {← go rhs})"
        else
          core e
      if (← config).shapes then
        let shape := shape (← Meta.inferType e)
        return s!"(◇ {shape} {basic})"
      else
        return basic

  core : Expr → EncodeM Expression
    | .fvar id          => encodeFVar id
    | .mvar id          => encodeMVar id
    | .sort lvl         => return s!"(sort {← encodeLevel lvl})"
    | .const name lvls  => encodeConst name lvls
    | .proj ty idx b    => encodeProj ty idx b
    | .app fn arg       => return s!"(app {← go fn} {← go arg})"
    | .lam _ ty b _     => encodeLambda ty b
    | .forallE _ ty b _ => encodeForall ty b
    | .lit (.strVal l)  => return s!"(lit {Json.renderString l})"
    | .lit (.natVal l)  => return s!"(lit {l})"
    | .bvar _           => panic! "'Egg.encode.core' found loose bvar"
    | _                 => panic! "'Egg.encode.core' received non-normalized expression"

  encodeFVar (id : FVarId) : EncodeM Expression := do
    if let some bvarName ← bvarName? id then
    return s!"(bvar {bvarName})"
    else return s!"(fvar {id.uniqueIdx!})"

  encodeMVar (id : MVarId) : EncodeM Expression := do
    if ← id.isAssignable
    then return s!"?{id.uniqueIdx!}"
    else return s!"(mvar {id.uniqueIdx!})"

  encodeLambda (ty b : Expr) : EncodeM Expression := do
    -- It's critical that we encode `ty` outside of the `withInstantiatedBVar` block, as otherwise
    -- the bvars in `encTy` are incorrectly shifted by 1.
    let encTy ← go ty
    withInstantiatedBVar ty b fun var? body => return s!"(λ {var?}{encTy} {← go body})"

  encodeForall (ty b : Expr) : EncodeM Expression := do
    -- It's critical that we encode `ty` outside of the `withInstantiatedBVar` block, as otherwise
    -- the bvars in `encTy` are incorrectly shifted by 1.
    let encTy ← go ty
    withInstantiatedBVar ty b fun var? body => return s!"(∀ {var?}{encTy} {← go body})"

  encodeConstLvls (lvls : List Level) : EncodeM Expression :=
    lvls.foldlM (init := "") (return s!"{·} {← encodeLevel ·}")

  encodeConst (name : Name) (lvls : List Level) : EncodeM Expression := do
    let env ← getEnv
    if let some projInfo ← getProjectionFnInfo? name then
      if let some (.ctorInfo { induct, .. }) := env.find? projInfo.ctorName then
        return s!"(proj \"{induct}\" {projInfo.i})"
    else if let some (.ctorInfo { induct, .. }) := env.find? name then
      if isStructure env induct then
        return s!"(mk \"{induct}\"{← encodeConstLvls lvls})"
    return s!"(const \"{name}\"{← encodeConstLvls lvls})"

  encodeProj (structName : Name) (idx : Nat) (body : Expr) : EncodeM Expression := do
    -- TODO: Is there a better way of obtaining the values of implicit arguments in the application,
    --       than calling `mkAppM`? What happens if some of them are supposed to be mvars? In that
    --       case it seems like it might be better to simply eliminate `proj` during normalization
    --       again.
    let some projFn := (getStructureFields (← getEnv) structName)[idx]?
      | throwError "'Egg.normalize' failed to encode 'proj'"
    let app ← Meta.mkAppM projFn #[body]
    go app
