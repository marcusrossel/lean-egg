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

-- TODO: The `stx?` argument is a workaround for (seemingly) not having `try catch` in
--       `CommandElabM`, which we would need in the elaborator for the `egg_basket` command.
def Extension.getBasket (ext : Extension) (key : Basket.Key) (stx? : Option Syntax := none) : CoreM Basket.Entries := do
  if let some basket := (ext.getState <| ← getEnv)[key]? then
    return basket
  else if let some stx := stx? then
    throwErrorAt stx "Unknown egg basket"
  else
    throwError "Unknown egg basket '{key}'"

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name  := `egg
    descr := "equality saturation theorem"
    applicationTime := .afterCompilation
    add entry stx attrKind := do
      -- TODO: I feel like we would want `resolveGlobalConstNoOverload`, but when we pass an
      --       identifier of the form `_root_.<name>` the `_root_` does not appear in the `entry`.
      let entry ← unresolveNameGlobal entry
      -- TODO: Validate the entry.
      match stx with
      | `(Parser.Attr.simple|egg $key:ident) => extension.add (key.getId, entry) attrKind
      | _                                    => throwError "'egg' attribute expectes a basket name"
  }

elab "egg_basket " dst:ident " extends " srcs:ident,+ : command => do
  for src in srcs.getElems do
    let src ← Elab.Command.liftCoreM <| extension.getBasket src.getId (stx? := src)
    for entry in src do
      extension.add (dst.getId, entry)
