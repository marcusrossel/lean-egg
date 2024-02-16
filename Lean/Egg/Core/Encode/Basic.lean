import Egg.Lean
import Egg.Core.Encode.EncodeM
import Lean
open Lean

namespace Egg

abbrev Expression := String

-- Note: The encoding of expression mvars and universe level mvars in rewrites relies on the fact
--       that their indices are also unique between eachother.

def encodeLevel : Level → Source → Expression
  | .zero,       _     => "0"
  | .succ l,     k     => s!"(succ {encodeLevel l k})"
  | .max l₁ l₂,  k     => s!"(max {encodeLevel l₁ k} {encodeLevel l₂ k})"
  | .imax l₁ l₂, k     => s!"(imax {encodeLevel l₁ k} {encodeLevel l₂ k})"
  | .mvar id,    .goal => s!"(uvar {id.uniqueIdx!})"
  | .mvar id,    _     => s!"?{id.uniqueIdx!}"
  | .param name, _     => s!"(param {name})"

open EncodeM IndexT

-- Note: This function expects its input expression to be normalized (cf. `Egg.normalize`).
partial def encode (e : Expr) (src : Source) (cfg : Config) : IndexT MetaM Expression :=
  Prod.fst <$> (go e).run { exprSrc := src, config := cfg }
where
  go (e : Expr) : EncodeM Expression := do
    if ← needsProofErasure e then return "proof" else
      let c ← core e
      if (← config).typeTags == .none || e.isSort || e.isForall then return c else
        let some tag ← getTypeTag? e | unreachable!
        return s!"(τ {tag} {c})"

  getTypeTag? (e : Expr) : EncodeM (Option Expression) := do
    let ty ← Meta.inferType e
    match (← config).typeTags with
    | .indices => return s!"{← typeIdx ty}"
    | .exprs   => withTypeTags .none do core ty
    | .none    => return none

  core : Expr → EncodeM Expression
    | .bvar idx         => return s!"(bvar {idx})"
    | .fvar id          => encodeFVar id
    | .mvar id          => encodeMVar id
    | .sort lvl         => return s!"(sort {encodeLevel lvl (← exprSrc)})"
    | .const name lvls  => return s!"(const {name}{← encodeULvls lvls})"
    | .app fn arg       => return s!"(app {← go fn} {← go arg})"
    | .lam _ ty b _     => withInstantiatedBVar ty b (return s!"(λ {← go ·})")
    | .forallE _ ty b _ => withInstantiatedBVar ty b (return s!"(∀ {← go ·})")
    | .lit (.strVal l)  => return s!"(lit \"{l}\")"
    | .lit (.natVal l)  => return s!"(lit {l})"
    | _                 => panic! "'Egg.encode.core' received non-normalized expression"

  encodeFVar (id : FVarId) : EncodeM Expression := do
    if let some bvarIdx ← bvarIdx? id
    then return s!"(bvar {bvarIdx})"
    else return s!"(fvar {id.uniqueIdx!})"

  encodeMVar (id : MVarId) : EncodeM Expression := do
    match ← exprSrc with
    | .goal => return s!"(mvar {id.uniqueIdx!})"
    | _     => return s!"?{id.uniqueIdx!}"

  encodeULvls (lvls : List Level) : EncodeM Expression := do
    if (← config).eraseULvls
    then return ""
    else return lvls.foldl (init := "") (s!"{·} {encodeLevel · (← exprSrc)}")
