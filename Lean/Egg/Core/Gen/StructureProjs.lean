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

/--
For the given rewrite (`target`), we iterate over all subterms and collect
 `structure`s that occur in them.

We use a list since we later want to `eraseDups`, but this function
does not exist for `Array`.
-/
private def getStructuresInRewrite (target : Rewrite)
   : MetaM (List Name) := do
   for c in target.conds do
     for ..
  return []

/--
To generate the structure projections, we first collect all the
structures that occur in the rewrites. For each structure, we
generate all the projections.
-/
def genStructureProjections (targets : Rewrites) (norm : Config.Normalization) (cfg : Config.Erasure) :
    MetaM Rewrites := do
      let structures ← targets.foldlM (init := []) fun rws rw => do
        return rws ++ (← getStructuresInRewrite rw)
      -- deduplicate names, convert to array
      structures.eraseDups
       |>.foldlM  (init := #[]) fun acc struct => do
        return acc ++ (← buildStructureProjEqns struct sorry)

mutual
/--
We only  get the structure projcetions
-/
private partial def getStructuresFromConstantInfo (info : ConstantInfo) : MetaM (Array Name) :=
  match info with
  | .inductInfo val => do
           match getStructureInfo? (← getEnv) val.name with
             | none => pure #[]
             | some structInfo => return #[structInfo.structName]
  | .defnInfo val => getStructureNames val.value
  | .thmInfo val => getStructureNames val.value
  | .ctorInfo val => getStructureNames (mkConst val.name)
  | .recInfo val => val.all.foldlM (init := #[])
    fun structs nm => do
      let newStructs ← getStructureNames (mkConst nm)
      return structs ++ newStructs
  | .quotInfo _ => pure #[]
  | .opaqueInfo _ =>  pure #[]
  | .axiomInfo _ => pure #[]

private partial def getStructureNames (e : Expr) : MetaM (Array Name) := do

  let env ← getEnv
  let rec visit (e : Expr) (currNames : Array Name) : MetaM (Array Name) := do
    match e with
    | Expr.const name _ =>
      match env.find? name with
        | some info  => do
          let newNames ← getStructuresFromConstantInfo info
          return currNames ++ newNames
        | none => pure currNames
    | Expr.app fn arg =>
      let fnNames ← visit fn currNames
      let argNames ← visit arg currNames
      return fnNames ++ argNames
    | Expr.lam _ _ body _ =>
      visit body currNames
    | Expr.forallE _ _ body _ =>
      visit body currNames
    | Expr.mdata _ b =>
      visit b currNames
    | Expr.letE _ _ val body _ =>
      let valNames ← visit val currNames
      let bodyNames ← visit body currNames
      return valNames ++ bodyNames
    | _ => pure currNames
  visit e #[]
end  --mutual

theorem foo : 1 + 1 = 2 := rfl

#eval show MetaM Unit from do
  let names ← getStructureNames (mkConst `foo)
  trace[Meta.debug] s!"Structure names: {names}"
