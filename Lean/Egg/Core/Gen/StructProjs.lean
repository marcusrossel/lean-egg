import Egg.Core.Rewrite.Rule
import Egg.Core.Guides

open Lean Std Meta Elab Term

namespace Egg

private structure StructInfo where
  projs : HashSet Nat           := ∅
  ctor  : Option ConstructorVal := none

private abbrev StructInfos := HashMap Name StructInfo

private def StructInfos.ofExpr (e : Expr) (init : StructInfos := ∅) : MetaM StructInfos := do
  match e with
  | .const c _                                       => ofConst c init
  | .app e₁ e₂ | .lam _ e₁ e₂ _ | .forallE _ e₁ e₂ _ => ofExpr e₂ (← ofExpr e₁ init)
  | .mdata .. | .letE .. | .proj ..                  => throwError "egg: internal error: 'Egg.StructInfo.ofExpr' received non-normalized expression"
  | _                                                => return init
where
  ofConst (const : Name) (infos : StructInfos) : MetaM StructInfos := do
    let env ← getEnv
    if let some projInfo ← getProjectionFnInfo? const then
      if let some (.ctorInfo { induct, .. }) := env.find? projInfo.ctorName then
        return infos.alterD induct {} fun info =>
          { info with projs := info.projs.insert projInfo.i }
    else if let some (.ctorInfo ctorInfo) := env.find? const then
      if isStructure env ctorInfo.induct then
        return infos.alterD ctorInfo.induct {} fun info =>
          { info with ctor := some ctorInfo }
    return infos

private def StructInfos.rules (infos : StructInfos) (cfg : Config.Normalization) : MetaM Rewrite.Rules := do
  let mut rules := ∅
  for (structName, info) in infos do
    let some ctor := info.ctor | continue
    for projIdx in info.projs do
      let ls ← mkFreshLevelMVarsFor (.ctorInfo ctor)
      let (mvars, _) ← forallMetaTelescope (ctor.type.instantiateLevelParams ctor.levelParams ls)
      let appCtor := mkAppN (.const ctor.name ls) mvars
      let some field := (getStructureFields (← getEnv) structName)[projIdx]?
        | throwError "Internal error in 'Egg.StructInfos.rws'"
      let lhs ← mkProjection appCtor field
      let rhs := mvars[ctor.numParams + projIdx]!
      let eq ← mkForallFVars mvars (← mkEq lhs rhs)
      let proof ← mkLambdaFVars mvars (← mkEqRefl lhs)
      let some rules' ← rules.add? (.structProj rules.rws.size) proof eq cfg (.dir .forward)
        | throwError "Internal error in 'Egg.StructInfos.rws'"
      rules := rules'
  return rules

private def Congr.structInfos (cgr : Congr) (init : StructInfos := ∅) : MetaM StructInfos := do
  StructInfos.ofExpr cgr.rhs (init := ← StructInfos.ofExpr cgr.lhs init)

private def Rewrite.Condition.structInfos (cond : Rewrite.Condition) (init : StructInfos := ∅) :
    MetaM StructInfos :=
  StructInfos.ofExpr cond.type init

private def Rewrite.structInfos (rw : Rewrite) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos ← rw.toCongr.structInfos init
  for cond in rw.conds.active do infos ← cond.structInfos (init := infos)
  return infos

private def Rewrite.Rules.structInfos (rules : Rewrite.Rules) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos := init
  for rule in rules.entries do infos ← rule.rw.structInfos (init := infos)
  return infos

private def Guide.structInfos (guide : Guide) (init : StructInfos := ∅) : MetaM StructInfos := do
  StructInfos.ofExpr guide.expr init

private def Guides.structInfos (guides : Guides) (init : StructInfos := ∅) : MetaM StructInfos := do
  let mut infos := init
  for guide in guides do infos ← guide.structInfos (init := infos)
  return infos

def genStructProjRws
    (goal : Congr) (rules : Rewrite.Rules) (guides : Guides) (cfg : Config.Normalization) :
    MetaM Rewrite.Rules := do
  (← goal.structInfos <| ← rules.structInfos <| ← guides.structInfos).rules cfg
