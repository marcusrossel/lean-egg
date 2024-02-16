namespace Egg.Config

inductive ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq

structure Encoding where
  eraseProofs        := true
  eraseConstLevels   := false
  eraseLambdaDomains := true
  eraseForallDomains := true
  deriving BEq

structure Gen where
  genTcProjRws := true
  genNatLitRws := true
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

def Config.noErasure : Config where
  eraseProofs        := false
  eraseConstLevels   := false
  eraseLambdaDomains := false
  eraseForallDomains := false
