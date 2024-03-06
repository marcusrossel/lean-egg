import Egg.Core.Config
import Lean
open Lean

namespace Egg

register_option egg.config.eraseProofs : Bool := {
  defValue := ({} : Config).eraseProofs
}

register_option egg.config.eraseLambdaDomains : Bool := {
  defValue := ({} : Config).eraseLambdaDomains
}

register_option egg.config.eraseForallDomains : Bool := {
  defValue := ({} : Config).eraseForallDomains
}

register_option egg.config.genTcProjRws : Bool := {
  defValue := ({} : Config).genTcProjRws
}

register_option egg.config.genNatLitRws : Bool := {
  defValue := ({} : Config).genNatLitRws
}

register_option egg.config.genEtaRw : Bool := {
  defValue := ({} : Config).genEtaRw
}

register_option egg.config.explode : Bool := {
  defValue := ({} : Config).explode
}

register_option egg.config.optimizeExpl : Bool := {
  defValue := ({} : Config).optimizeExpl
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
    toDebug            := {}
  }
