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

/--
This function gathers the `Name`s of structures occuring in a constant.

We don't want to make this mutually recursive with `getStructureNames`
because we don't want to dig up `structure`s that where the constructors
or projections won't occur in an `egg` proof.
-/
private def getStructureFromConstantInfo (info : ConstantInfo) : MetaM (Option Name) :=
  match info with
  | .inductInfo val => do
           match getStructureInfo? (← getEnv) val.name with
             | none => pure none
             | some structInfo => pure structInfo.structName
  | .ctorInfo val => do
           match getStructureInfo? (← getEnv) val.name with
             | none => pure none
             | some structInfo => pure structInfo.structName
  | _ => pure none

/--
This function walks over an expression and collects the names of all
`structure`s in subexpressions.
-/
private def getStructureNames (e : Expr) : MetaM (Array Name) := do

  let env ← getEnv
  let rec visit (e : Expr) (currNames : Array Name) : MetaM (Array Name) := do
    match e with
    | Expr.const name _ =>
      match env.find? name with
        | some info  => do
          let newName? ← getStructureFromConstantInfo info
          match newName? with
            | some newName => return currNames.push newName
            | none => pure currNames
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


#eval show MetaM Unit from do
  let names ← getStructureNames (mkConst `Prod)
  logInfo s!"Structure names: {names}"

theorem foo : (1,2).snd = 1 + 1 := rfl

#eval show MetaM Unit from do
  let constinfo ← getConstInfo `foo
  let names ← getStructureNames constinfo.value!
  logInfo s!"Structure names of {constinfo.value!}: {names}"

set_option pp.raw true in
#reduce (1,2)

def pair : Prod Nat Nat := (1,2)

instance : ToString ConstantInfo := ⟨fun cinfo => match cinfo with
 | .axiomInfo  val => "Axiom: {val}"
 | .defnInfo   val => "Defn: {val}"
 | .thmInfo    val => "Thm: {val}"
 | .opaqueInfo val => "Opaque: {val}"
 | .quotInfo   val => "Quot: {val}"
 | .inductInfo val => "Induct: {val}"
 | .ctorInfo   val => "Ctor: {val}"
 | .recInfo    val => "Rec: {val}"
 ⟩

#eval show MetaM Unit from do
  let constinfo ← getConstInfo `pair
  match constinfo.value! with
    | Expr.app (Expr.app (Expr.app (Expr.app fn arg₁) arg₂) arg₃) arg₄ => do
       logInfo s!"Function: {fn}"
       logInfo s!"Arg: {arg₁}"
       logInfo s!"Arg: {arg₂}"
       logInfo s!"Arg: {arg₃}"
       logInfo s!"Arg: {arg₄}"
       let some (nm, _) := fn.const?
         | throwError "Expected constant"
       let constInfo ← getConstInfo nm
       logInfo s!"Constant info: {constInfo}"
       logInfo s!"structureFromConstantInfo {← getStructureFromConstantInfo constInfo}"
    | _ => pure ()
