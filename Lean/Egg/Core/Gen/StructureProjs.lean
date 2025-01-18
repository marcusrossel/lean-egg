import Lean
open Lean Syntax

syntax (name := projfns) "#projfns " ident : command

private def printStructId (id : Syntax) : Elab.Command.CommandElabM Unit := do --Elab.Command.CommandElabM Unit := do
    let structName := id.getId
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
               logInfo s!"Constructor: {ctorVal.name}"
               for fieldInfo in structInfo.fieldInfo do
                 logInfo s!"Field {fieldInfo.fieldName}: {fieldInfo.projFn}"
        | _ => throwError s!"{structName} is not a structure"

@[command_elab projfns]
def elabProjFns : Elab.Command.CommandElab
  | `(#projfns%$tk  $id:ident) => withRef tk <| printStructId id
  | _                       => throwError "invalid #print command"

structure Point where
  x : Nat
  y : Nat

#projfns Point
