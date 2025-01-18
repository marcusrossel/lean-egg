import Lean
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

private def buildStructureProjEqns (structName : Name) : MetaM <| Array (Expr × Expr) := do
  let (ctor, projs) ← getStructureCtorAndProjs structName
  let mvars ← projs.mapM
    fun pr => Meta.mkFreshExprMVar none (userName := pr)
  let ctorApp := mkAppN (mkConst ctor) mvars
  let rws := projs.zipWithIndex.map
    fun (proj, idx) =>
      (mkApp (mkConst proj) ctorApp, mvars[idx]!)
  return rws

syntax (name := projfns) "#projfns " ident : command
@[command_elab projfns]
def elabProjFns : Elab.Command.CommandElab
  | `(#projfns $id:ident) => do
    let rws ← Elab.Command.liftTermElabM <| buildStructureProjEqns id.getId
    for rw in rws do
      logInfo m!"{rw.1} -> {rw.2}"
  | _ => throwError "invalid #projfns command"

structure Point where
  x : Nat
  y : Nat

set_option pp.rawOnError true in
#projfns Point
