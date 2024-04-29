import Lean

open Lean

namespace Egg

/--
This validates that a theorem can be used by the `egg` tactic (it ultimately boils down to an equality.)

Unimplemented: Currently, this is a noop.
-/
def validateEggTheorem : Name → AttrM Unit := fun _ => pure ()

-- Ideally this should be at some point a discrimination tree
abbrev EggTheorems := Array Name

abbrev EggEntry := Name -- later: Lean.Meta.SimpEntry

def addEggTheoremEntry (d : EggTheorems) (e : EggEntry) : EggTheorems :=
  d.push e

abbrev EggXtension := SimpleScopedEnvExtension EggEntry EggTheorems

open Lean.Elab
open Lean.Elab.Command

def EggXtension.getTheorems (ext : EggXtension) : CoreM EggTheorems :=
  return ext.getState (← getEnv)

/--
This function does the appropriate preprocessing from a `Name` to record a theorem as
an `egg` theorem.

For now, this preprocessing is nothing (just store the name in a singleton `Array`).
However, in the future this can be used like simp to do more efficient preprocessing
and deal with other kinds of `egg` lemmas (or even import `simp` lemmas).
-/
private def mkEggTheoremsFromConst (declName : Name) : MetaM EggTheorems :=
  pure #[declName]

def addEggTheorem (ext : EggXtension) (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let eggThms ← mkEggTheoremsFromConst declName
  for eggThm in eggThms do
    ext.add eggThm attrKind

def mkEggXt (name : Name := by exact decl_name%) : IO EggXtension :=
  registerSimpleScopedEnvExtension {
    name     := name
    initial  := {}
    addEntry := fun d e => addEggTheoremEntry d e
  }

def mkEggAttr (attrName : Name) (attrDescr : String) (ext : EggXtension)
    (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref   := ref
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName _stx attrKind => do
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        if (← Meta.isProp info.type) then
          addEggTheorem ext declName attrKind
        else
          throwError "invalid 'egg', it is not a proposition"
      discard <| go.run {} {}
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      let s := s.erase (declName)
      modifyEnv fun env => ext.modifyState env fun _ => s
  }


abbrev EggXtensionMap := HashMap Name EggXtension

builtin_initialize eggXtensionMapRef : IO.Ref EggXtensionMap ← IO.mkRef {}

def registerEggAttr (attrName : Name) (attrDescr : String)
    (ref : Name := by exact decl_name%) : IO EggXtension := do
  let ext ← mkEggXt ref
  mkEggAttr attrName attrDescr ext ref -- Remark: it will fail if it is not performed during initialization
  eggXtensionMapRef.modify fun map => map.insert attrName ext
  return ext

builtin_initialize eggXtension : EggXtension ← registerEggAttr `egg "equality saturation theorem theorem"


syntax (name := showEgg) "#show_egg_set" : command

--
--
--#check Lean.Meta.mkSimpAttr
--
--@[command_elab insertEgg] def elabInsertEgg : CommandElab := fun stx => do
--  IO.println s!"inserting {stx[1].getId}"
--  modifyEnv fun env => eggXtension.addEntry env stx[1].getId
--
@[command_elab showEgg] def elabShowEgg : CommandElab := fun _ => do
  IO.println s!"egg set: {eggXtension.getState (← getEnv) |>.toList}"
--
--
--initialize eggTag : TagAttribute ←
--  registerTagAttribute `egg "Tag for marking lemmas used for equality saturation" (validate := validateEggTheorem)

end Egg
