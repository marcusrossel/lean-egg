import Lean

open Lean

initialize eggXtension : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := NameSet.insert
    addImportedFn := fun es => mkStateFromImportedEntries NameSet.insert {} es
  }

syntax (name := insertEgg) "insert_egg " ident : command
syntax (name := showEgg) "show_gg_set" : command

open Lean.Elab
open Lean.Elab.Command

@[command_elab insertEgg] def elabInsertEgg : CommandElab := fun stx => do
  IO.println s!"inserting {stx[1].getId}"
  modifyEnv fun env => eggXtension.addEntry env stx[1].getId

@[command_elab showEgg] def elabShowBla : CommandElab := fun _ => do
  IO.println s!"egg set: {eggXtension.getState (← getEnv) |>.toList}"

initialize eggTag : TagAttribute ←
  registerTagAttribute `egg "Tag for marking lemmas used for equality saturation"
