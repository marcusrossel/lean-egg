import Egg.Core.Config
import Lean
open Lean Meta Core

namespace Egg

-- Instantiates mvars, performs ζ-, converts `Expr.proj`s to `Expr.app`s, and removes `Expr.mdata`s.
-- Depending on the `cfg`, also performs β- and η-reduction and reduction of internalized natural
-- number operations.
partial def normalize (e : Expr) (cfg : Config.Normalization) : MetaM Expr := do
  go (← instantiateMVars e)
where
  go : Expr → MetaM Expr
    | .mdata _ e  => go e
    | .app fn arg => do
      let mut app := .app (← go fn) (← go arg)
      if cfg.betaReduceRws then app ← betaReduce app
      if cfg.natReduceRws  then app ← natReduce app
      return app
    | .lam n ty b i => do
      withLocalDecl n i (← go ty) fun fvar => do
        let body ← mkLambdaFVars #[fvar] (← go <| b.instantiate1 fvar)
        return if cfg.etaReduceRws then body.eta else body
    | .forallE n ty b i => do
      withLocalDecl n i (← go ty) fun fvar => do
        mkForallFVars #[fvar] (← go <| b.instantiate1 fvar)
    | .proj ty idx b => return .proj ty idx (← go b)
    | e@(.letE ..)   => do go (← zetaReduce e)
    | e              => return e

  natReduce (e : Expr) : MetaM Expr := do
    if let some n ← evalNat e
    then return mkNatLit n
    else return e
