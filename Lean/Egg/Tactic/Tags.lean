import Lean
open Lean hiding HashMap
open Std (HashMap)

namespace Egg

abbrev Basket.Key := Name

-- TODO: Have this be a `Lean.Meta.SimpEntry`.
abbrev Basket.Entry := Name

-- TODO: Have this be a discrimination tree.
abbrev Basket.Entries := Array Basket.Entry

open Basket in
abbrev Extension := SimpleScopedEnvExtension (Key × Entry) (HashMap Key Entries)

initialize extension : Extension ← registerSimpleScopedEnvExtension {
  initial    := ∅,
  addEntry s := fun ⟨key, entry⟩ => s.alter key (·.getD #[] |>.push entry)
}

def Extension.getBasket (ext : Extension) (key : Basket.Key) : CoreM Basket.Entries :=
  return (ext.getState <| ← getEnv)[key]?.getD #[]

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name  := `egg
    descr := "equality saturation theorem"
    applicationTime := .afterCompilation
    add entry stx attrKind :=
      -- TODO: Validate the entry.
      match stx with
      | `(Parser.Attr.simple|egg $key:ident) => extension.add (key.getId, entry) attrKind
      | _                                    => throwError "'egg' attribute expectes a basket name"
  }
