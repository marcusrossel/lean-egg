namespace Egg.Config

structure Encoding where
  eraseProofs        := true
  eraseLambdaDomains := false
  eraseForallDomains := false
  betaReduceRws      := true
  etaReduceRws       := true
  deriving BEq

structure Gen where
  genTcProjRws := true
  genNatLitRws := true
  genEtaRw     := true
  genBetaRw    := true
  explode      := true
  deriving BEq

structure Backend where
  blockInvalidMatches := true
  shiftCapturedBVars  := true
  optimizeExpl        := false
  deriving BEq

inductive Debug.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq, Inhabited

structure Debug where
  exitPoint  : Debug.ExitPoint := .none
  vizPath    : Option String   := none
  traceSubstitutions           := false
  traceCapturedBVarShifting    := false
  deriving BEq

end Config
open Config

structure Config extends Encoding, Gen, Backend, Debug
