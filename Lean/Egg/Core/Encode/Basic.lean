import Egg.Lean
import Egg.Core.Encode.EncodeM

namespace Lean

open Egg (Expression Source EncodeM IndexT)
open Egg.EncodeM
open Egg.IndexT

-- Note: The encoding of expression mvars and universe level mvars in rewrites relies on the fact
--       that their indices are also unique between eachother.

-- BUG?: Should params be encoded as (coordinated) mvars within rewrites?
def Level.toEgg : Level → Source → MetaM Egg.Expression
  | .zero,       _     => return "0"
  | .succ l,     k     => return s!"(succ {← l.toEgg k})"
  | .max l₁ l₂,  k     => return s!"(max {← l₁.toEgg k} {← l₂.toEgg k})"
  | .imax l₁ l₂, k     => return s!"(imax {← l₁.toEgg k} {← l₂.toEgg k})"
  | .mvar id,    .goal => return s!"(uvar {id.uniqueIdx!})"
  | .mvar id,    _     => return s!"?{id.uniqueIdx!}"
  | .param name, _     => return s!"(param {name})"

partial def Expr.toEgg (e : Expr) (src : Source) (cfg : Egg.Config) : IndexT MetaM Expression :=
  Prod.fst <$> (go e).run { exprSrc := src, config := cfg }
where
  go (e : Expr) : EncodeM Expression := do
    if ← needsProofErasure e then return "proof" else
      let c ← encode e
      -- TODO: What happens here when we have a leading `mdata`?
      if (← config).typeTags == .none || e.isSort || e.isForall then return c else
        let some tag ← getTypeTag? e | unreachable!
        return s!"(τ {tag} {c})"

  getTypeTag? (e : Expr) : EncodeM (Option Expression) := do
    let ty ← Meta.inferType e
    match (← config).typeTags with
    | .indices => return s!"{← typeIdx ty}"
    | .exprs   => withTypeTags .none do encode ty
    | .none    => return none

  -- TODO: Reconsider how to handle the binder type of a `forallE` in the typed and untyped settings.
  encode : Expr → EncodeM Expression
    | bvar idx         => return s!"(bvar {idx})"
    | fvar id          => encodeFVar id
    | mvar id          => encodeMVar id
    | sort lvl         => return s!"(sort {← lvl.toEgg (← exprSrc)})"
    | const name lvls  => encodeConst name lvls
    | app fn arg       => encodeApp fn arg
    | lam _ ty b _     => withEmptyAppArgs do withInstantiatedBVar ty b (return s!"(λ {← go ·})")
    | forallE _ ty b _ => withEmptyAppArgs do withInstantiatedBVar ty b (return s!"(∀ {← go ty} {← go ·})")
    | lit (.strVal l)  => return s!"(lit \"{l}\")"
    | lit (.natVal l)  => return s!"(lit {l})"
    | mdata _ e        => go e
    | e@(letE ..)      => do go (← Meta.zetaReduce e)
    | proj ty ctor b   => encodeProj ty ctor b

  encodeFVar (id : FVarId) : EncodeM Expression := do
    if let some bvarIdx ← bvarIdx? id
    then return s!"(bvar {bvarIdx})"
    else return s!"(fvar {id.uniqueIdx!})"

  encodeMVar (id : MVarId) : EncodeM Expression := do
    match ← exprSrc with
    | .goal => return s!"(mvar {id.uniqueIdx!})"
    | _     => return s!"?{id.uniqueIdx!}"

  encodeConst (name : Name) (lvls : List Level) : EncodeM Expression := do
    saveTcProjIfApplicable name lvls
    return s!"(const {name}{← encodeULvls lvls})"

  encodeApp (fn arg : Expr) : EncodeM Expression := do
    let eFn ← withAppArg arg do go fn
    let eArg ← withEmptyAppArgs do go arg
    return s!"(app {eFn} {eArg})"

  encodeProj (ty : Name) (ctor : Nat) (b : Expr) : EncodeM Expression := do
    let env ← getEnv
    let some field := (getStructureFields env ty)[ctor]? | throwError "egg: failed to encode proj"
    let some prj   := getProjFnForField? env ty field    | throwError "egg: failed to encode proj"
    let some info  := env.find? prj                      | throwError "egg: failed to encode proj"
    let lParams    := info.levelParams.map (Level.param ·)
    let expr       := Expr.app (.const prj lParams) b
    go expr

  encodeULvls (lvls : List Level) : EncodeM String := do
    if (← config).eraseULvls
    then return ""
    else lvls.foldlM (init := "") fun res lvl => return s!"{res} {← lvl.toEgg (← exprSrc)}"
