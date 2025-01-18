import Lean
import Egg.Core.Premise.Rewrites

open Lean Syntax

private def getStructureCtorAndProjs (structName : Name) : MetaM (Name × Array Name) := do --Elab.Command.CommandElabM Unit := do
    let env ← getEnv
    match env.find? structName with
    | none => throwError s!"Structure {structName} not found"
    | some constInfo =>
      match constInfo with
        | .inductInfo _ => do
           match getStructureInfo? env structName with
             | none => throwError s!"{structName} is inductive but not a structure"
             | some structInfo => do
               let ctorVal := getStructureCtor env structName
               --logInfo s!"Constructor: {ctorVal.name}"
               let projs := structInfo.fieldNames.map
                 fun nm => structInfo.structName.append nm
               return (ctorVal.name, projs)
        | _ => throwError s!"{structName} is not a structure"

open Egg

private def buildStructureProjEqns (structName : Name) (cfg : Rewrite.Config) : MetaM Rewrites := do
  let (ctor, projs) ← getStructureCtorAndProjs structName
  let mvars ← projs.mapM
    fun pr => Meta.mkFreshExprMVar none (userName := pr)
  let ctorApp := mkAppN (mkConst ctor) mvars
  let rawRws := projs.zipWithIndex.map
    fun (proj, idx) =>
      (mkApp (mkConst proj) ctorApp, mvars[idx]!)
  let mut rws := []
  for (lhs, rhs) in rawRws do
    let rw ← Rewrite.mkDefEq lhs rhs cfg
    rws := rw :: rws
  return rws.toArray
