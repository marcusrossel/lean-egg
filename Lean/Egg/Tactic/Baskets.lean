import Lean

open Lean Std

namespace Egg.Basket

abbrev Key := Name

inductive Value where
  | parent (key : Key)
  | premise (n : Name)
  deriving Inhabited

structure Entry where
  key : Key
  val : Value
  deriving Inhabited

structure Info where
  parents : HashSet Key
  prems   : HashSet Name

def Info.add (info : Info) : Value → Info
  | .parent p  => { info with parents := info.parents.insert p }
  | .premise n => { info with prems := info.prems.insert n }

instance : EmptyCollection Info where
  emptyCollection := { parents := ∅, prems := ∅ }

end Basket

open Basket in
abbrev Extension := SimpleScopedEnvExtension Entry (HashMap Key Info)

initialize extension : Extension ← registerSimpleScopedEnvExtension {
  initial := ∅
  addEntry infos entry := infos.alter entry.key (·.getD ∅ |>.add entry.val)
}

namespace Extension

-- NOTE: The `stx?` argument is a workaround for (seemingly) not having `try catch` in
--       `CommandElabM`, which we would need in the elaborator for the `egg_basket` command.
def getBasket (ext : Extension) (key : Basket.Key) (stx? : Option Syntax := none) :
    CoreM Basket.Info := do
  if let some basket := (ext.getState <| ← getEnv)[key]? then
    return basket
  else if let some stx := stx? then
    throwErrorAt stx "Unknown egg basket"
  else
    throwError "Unknown egg basket '{key}'"

partial def getAllBasketPremises (ext : Extension) (key : Basket.Key) : CoreM (Array Name) := do
  return (← go key).toArray.insertionSort Name.lt
where
  go (key : Basket.Key) : CoreM (HashSet Name) := do
    let info ← ext.getBasket key
    let mut prems := info.prems
    for parent in info.parents do
      prems := prems.union (← go parent)
    return prems

partial def basketContains (ext : Extension) (key : Basket.Key) (premise : Name) : CoreM Bool := do
  let info ← ext.getBasket key
  if info.prems.contains premise then return true
  for parent in info.parents do
    if ← ext.basketContains parent premise then return true
  return false

end Extension

initialize
  -- TODO: I'm guessing we should use some other function, which does not mention "builtin".
  registerBuiltinAttribute {
    name  := `egg
    descr := "equality saturation theorem"
    applicationTime := .afterCompilation
    add premise stx attrKind := do
      -- TODO: I feel like we would want `resolveGlobalConstNoOverload`, but when we pass an
      --       identifier of the form `_root_.<name>` the `_root_` does not appear in the `entry`.
      let premise ← unresolveNameGlobal premise
      -- TODO: Validate the entry.
      match stx with
      | `(Parser.Attr.simple|egg $key:ident) => extension.add ⟨key.getId, .premise premise⟩ attrKind
      | _                                    => throwError "'egg' attribute expectes a basket name"
  }

syntax egg_basket_thms := " with " ident,+

elab "egg_basket " key:ident " extends " parents:ident,+ prems?:(egg_basket_thms)? : command => do
  for parent in parents.getElems do
    extension.add { key := key.getId, val := .parent parent.getId }
  let some prems := prems? | return
  let `(egg_basket_thms| with $prems,*) := prems | return
  for premise in prems.getElems do
    extension.add { key := key.getId, val := .premise premise.getId }

private partial def basketMsg (key : Name) (stx? : Option Syntax := none) :
    Elab.Command.CommandElabM MessageData := do
  let info ← Elab.Command.liftCoreM do extension.getBasket key stx?
  let premises := info.prems.toList.mergeSort Name.lt |>.map MessageData.ofConstName
  let mut msg := .joinSep premises ", "
  for parent in info.parents do
    let parentHeader := m!"* extends {parent.toString}:"
    let parentBody := indentD (← basketMsg parent)
    msg := m!"{msg}\n{parentHeader}{parentBody}"
  return msg

elab "#egg_basket " key:ident : command => do
  logInfo (← basketMsg key.getId key.raw)
