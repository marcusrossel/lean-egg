import Egg.Lean
import Egg.Core.Encode.EncodeM

namespace Lean

-- Note: The encoding of expression mvars and universe level mvars in rewrites relies on the fact
--       that their indices are also unique between eachother.

def Level.toEgg : Level → Egg.Expression.Kind → Egg.Expression
  | .zero,       _     => "0"
  | .succ l,     k     => s!"(succ {l.toEgg k})"
  | .max l₁ l₂,  k     => s!"(max {l₁.toEgg k} {l₂.toEgg k})"
  | .imax l₁ l₂, k     => s!"(imax {l₁.toEgg k} {l₂.toEgg k})"
  | .mvar id,    .goal => s!"(uvar {id.uniqueIdx!})"
  | .mvar id,    .rw   => s!"?{id.uniqueIdx!}"
  | .param name, _     => s!"(param {name})"

open Egg (EncodeM IndexT)
open Egg.EncodeM
open Egg.IndexT

partial def Expr.toEgg (e : Expr) (kind : Egg.Expression.Kind) (cfg : Egg.Config) :
    IndexT MetaM Egg.Expression :=
  Prod.fst <$> (go e).run { exprKind := kind, config := cfg }
where
  go (e : Expr) : EncodeM Egg.Expression := do
    if ← needsProofErasure e then return "proof" else
      let c ← encode e
      -- TODO: What happens here when we have a leading `mdata`?
      if (← config).typeTags == .none || e.isSort || e.isForall then return c else
        let some tag ← getTypeTag? e | unreachable!
        return s!"(τ {tag} {c})"

  getTypeTag? (e : Expr) : EncodeM (Option Egg.Expression) := do
    let ty ← Meta.inferType e
    match (← config).typeTags with
    | .indices => return s!"{← typeIdx ty}"
    | .exprs   => withTypeTags .none do encode ty
    | .none    => return none

  -- TODO: Reconsider how to handle the binder type of a `forallE` in the typed and untyped settings.
  encode : Expr → EncodeM Egg.Expression
    | bvar idx         => return s!"(bvar {idx})"
    | fvar id          => encodeFVar id
    | mvar id          => encodeMVar id
    | sort lvl         => return s!"(sort {lvl.toEgg (← exprKind)})"
    | const name lvls  => return s!"(const {name}{← encodeULvls lvls})"
    | app fn arg       => return s!"(app {← go fn} {← go arg})"
    | lam _ ty b _     => withInstantiatedBVar ty b (return s!"(λ {← go ·})")
    | forallE _ ty b _ => withInstantiatedBVar ty b (return s!"(∀ {← go ty} {← go ·})")
    | lit (.strVal l)  => return s!"(lit \"{l}\")"
    | lit (.natVal l)  => return s!"(lit {l})"
    | mdata _ e        => go e
    | e@(letE ..)      => do go (← Meta.zetaReduce e)
    | proj ty ctor b   => encodeProj ty ctor b

  encodeFVar (id : FVarId) : EncodeM Egg.Expression := do
    if let some bvarIdx ← bvarIdx? id
    then return s!"(bvar {bvarIdx})"
    else return s!"(fvar {id.uniqueIdx!})"

  encodeMVar (id : MVarId) : EncodeM Egg.Expression := do
    match ← exprKind with
    | .goal => return s!"(mvar {id.uniqueIdx!})"
    | .rw   => return s!"?{id.uniqueIdx!}"

  encodeProj (ty : Name) (ctor : Nat) (b : Expr) : EncodeM Egg.Expression := do
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
    else return lvls.foldl (init := "") (s!"{·} {·.toEgg (← exprKind)}")
