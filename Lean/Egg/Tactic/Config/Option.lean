import Egg.Core.Config
import Lean
open Lean

namespace Egg

register_option egg.eraseProofs : Bool := {
  defValue := ({} : Config).eraseProofs
}

register_option egg.eraseLambdaDomains : Bool := {
  defValue := ({} : Config).eraseLambdaDomains
}

register_option egg.eraseForallDomains : Bool := {
  defValue := ({} : Config).eraseForallDomains
}

register_option egg.genTcProjRws : Bool := {
  defValue := ({} : Config).genTcProjRws
}

register_option egg.genNatLitRws : Bool := {
  defValue := ({} : Config).genNatLitRws
}

register_option egg.genEtaRw : Bool := {
  defValue := ({} : Config).genEtaRw
}

register_option egg.genBetaRw : Bool := {
  defValue := ({} : Config).genBetaRw
}

register_option egg.explode : Bool := {
  defValue := ({} : Config).explode
}

register_option egg.blockInvalidMatches : Bool := {
  defValue := ({} : Config).blockInvalidMatches
}

register_option egg.shiftCapturedBVars : Bool := {
  defValue := ({} : Config).shiftCapturedBVars
}

register_option egg.optimizeExpl : Bool := {
  defValue := ({} : Config).optimizeExpl
}

def Config.fromOptions : MetaM Config := return {
    eraseLambdaDomains  := egg.eraseLambdaDomains.get (← getOptions)
    eraseProofs         := egg.eraseProofs.get (← getOptions)
    eraseForallDomains  := egg.eraseForallDomains.get (← getOptions)
    genTcProjRws        := egg.genTcProjRws.get (← getOptions)
    genNatLitRws        := egg.genNatLitRws.get (← getOptions)
    genEtaRw            := egg.genEtaRw.get (← getOptions)
    genBetaRw           := egg.genBetaRw.get (← getOptions)
    explode             := egg.explode.get (← getOptions)
    blockInvalidMatches := egg.blockInvalidMatches.get (← getOptions)
    shiftCapturedBVars  := egg.shiftCapturedBVars.get (← getOptions)
    optimizeExpl        := egg.optimizeExpl.get (← getOptions)
    toDebug             := {}
  }
