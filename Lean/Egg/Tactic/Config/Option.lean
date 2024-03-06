import Egg.Core.Config
import Lean
open Lean

namespace Egg

instance : KVMap.Value Egg.Config.Debug.ExitPoint where
  toDataValue
    | .none        => (0 : Nat)
    | .beforeEqSat => (1 : Nat)
    | .beforeProof => (2 : Nat)
  ofDataValue?
    | (0 : Nat) => some .none
    | (1 : Nat) => some .beforeEqSat
    | (2 : Nat) => some .beforeProof
    | _         => none

instance : KVMap.Value (Option String) where
  toDataValue s? := s?.getD ""
  ofDataValue?
    | (s : String) => s
    | _            => none

register_option egg.config.eraseProofs : Bool := {
  defValue := true
}

register_option egg.config.eraseLambdaDomains : Bool := {
  defValue := false
}

register_option egg.config.eraseForallDomains : Bool := {
  defValue := false
}

register_option egg.config.genTcProjRws : Bool := {
  defValue := true
}

register_option egg.config.genNatLitRws : Bool := {
  defValue := true
}

register_option egg.config.genEtaRw : Bool := {
  defValue := true
}

register_option egg.config.explode : Bool := {
  defValue := false
}

register_option egg.config.optimizeExpl : Bool := {
  defValue := false
}

register_option egg.config.exitPoint : Egg.Config.Debug.ExitPoint := {
  defValue := .none
}

register_option egg.config.vizPath : Option String := {
  defValue := none
}

def Config.fromOptions : MetaM Config := return {
    eraseLambdaDomains := egg.config.eraseLambdaDomains.get (← getOptions)
    eraseProofs        := egg.config.eraseProofs.get (← getOptions)
    eraseForallDomains := egg.config.eraseForallDomains.get (← getOptions)
    genTcProjRws       := egg.config.genTcProjRws.get (← getOptions)
    genNatLitRws       := egg.config.genNatLitRws.get (← getOptions)
    genEtaRw           := egg.config.genEtaRw.get (← getOptions)
    explode            := egg.config.explode.get (← getOptions)
    optimizeExpl       := egg.config.optimizeExpl.get (← getOptions)
    exitPoint          := egg.config.exitPoint.get (← getOptions)
    vizPath            := egg.config.vizPath.get (← getOptions)
  }
