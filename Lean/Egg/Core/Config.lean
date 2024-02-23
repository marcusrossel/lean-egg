namespace Egg.Config

inductive ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq

structure Encoding where
  eraseProofs        := true
  eraseLambdaDomains := false
  eraseForallDomains := false
  deriving BEq

structure Gen where
  genTcProjRws := true
  genNatLitRws := true
  explode      := true
  deriving BEq

structure Backend where
  optimizeExpl := false
  deriving BEq

structure Debug where
  exitPoint := Config.ExitPoint.none
  deriving BEq

end Config
open Config

structure Config extends Encoding, Gen, Backend, Debug
