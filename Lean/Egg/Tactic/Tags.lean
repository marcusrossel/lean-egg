import Lean
open Lean hiding HashMap
open Std (HashMap)

namespace Egg

-- TODO: Have this be a `Lean.Meta.SimpEntry`.
abbrev Basket.Entry := Name

-- TODO: Have this be a discrimination tree.
abbrev Basket := Array Basket.Entry

abbrev Extension := SimpleScopedEnvExtension Basket.Entry Basket

namespace Extension

def getBasket (ext : Extension) : CoreM Basket :=
  return ext.getState (← getEnv)

def addEntry (ext : Extension) (entry : Basket.Entry) (kind : AttributeKind) : MetaM Unit := do
  -- TODO: Validate the entry.
  ext.add entry kind

abbrev Map := Std.HashMap Name Extension

initialize mapRef : IO.Ref Map ← IO.mkRef {}

-- Remark: `registerAttribute` will fail if it is not performed during initialization.
def register (attrName : Name) (attrDescr : String) (name := decl_name%) : IO Extension := do
  let ext ← registerSimpleScopedEnvExtension { name, initial := #[], addEntry := Array.push }
  registerAttribute attrName attrDescr ext name
  mapRef.modify (·.insert attrName ext)
  return ext
where
  registerAttribute (name : Name) (descr : String) (ext : Extension) (ref := decl_name%) : IO Unit :=
    -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
    registerBuiltinAttribute {
      ref, name, descr
      applicationTime := .afterCompilation
      add   := fun entry _ attrKind => discard <| (ext.addEntry entry attrKind).run {} {}
      erase := fun entry => modifyEnv fun env => ext.modifyState env (·.erase entry)
    }

end Extension

initialize extension : Extension ← Extension.register `egg "equality saturation theorem"
