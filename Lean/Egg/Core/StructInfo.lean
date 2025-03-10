import Egg.Core.Premise.Rewrites
import Egg.Core.Guides
import Lean
import Std

open Lean hiding HashMap
open Std (HashMap)
open Meta Elab Term

namespace Egg

structure StructInfo where
  params : Nat
  fields : Nat

abbrev StructInfos := HashMap Name StructInfo

-- Note: We only consider structures for which there appears a (naive or internalized) projection.
private def StructInfos.ofExpr (e : Expr) (init : StructInfos := ∅) : MetaM StructInfos := do
  match e with
  | .const c _                                       => ofConst c init
  | .proj ty _ b                                     => ofExpr b (← ofStructName ty init)
  | .app e₁ e₂ | .lam _ e₁ e₂ _ | .forallE _ e₁ e₂ _ => ofExpr e₂ (← ofExpr e₁ init)
  | .mdata .. | .letE ..                             => throwError "egg: internal error: 'Egg.StructInfo.ofExpr' received non-normalized expression"
  | _                                                => return init
where
  ofConst (const : Name) (infos : StructInfos) : MetaM StructInfos := do
    let some structName := (← getEnv).getProjectionStructureName? const | return infos
    ofStructName structName infos

  ofStructName (name : Name) (infos : StructInfos) : MetaM StructInfos := do
    if infos.contains name then                                        return infos
    let some { fieldNames, .. } := getStructureInfo? (← getEnv) name | return infos
    let some (.inductInfo inductInfo) := (← getEnv).find? name       | return infos
    return infos.insert name {
      params := inductInfo.numParams
      fields := fieldNames.size
    }

def Congr.structInfos (cgr : Congr) (init : StructInfos := ∅) : MetaM StructInfos := do
  StructInfos.ofExpr cgr.rhs (init := ← StructInfos.ofExpr cgr.lhs init)

def Rewrite.Condition.structInfos (cond : Rewrite.Condition) (init : StructInfos := ∅) : MetaM StructInfos :=
  StructInfos.ofExpr cond.type init

def Rewrite.structInfos (rw : Rewrite) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos ← rw.toCongr.structInfos init
  for cond in rw.conds do infos ← cond.structInfos (init := infos)
  return infos

def Rewrites.structInfos (rws : Rewrites) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos := init
  for rw in rws do infos ← rw.structInfos (init := infos)
  return infos

def Guide.structInfos (guide : Guide) (init : StructInfos := ∅) : MetaM StructInfos := do
  StructInfos.ofExpr guide.expr init

def Guides.structInfos (guides : Guides) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos := init
  for guide in guides do infos ← guide.structInfos (init := infos)
  return infos
