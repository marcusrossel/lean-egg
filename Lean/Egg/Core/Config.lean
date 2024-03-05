namespace Egg.Config

structure Encoding where
  eraseProofs        := true
  eraseLambdaDomains := false
  eraseForallDomains := false
  deriving BEq

structure Gen where
  genTcProjRws := true
  genNatLitRws := true
  genEtaRw     := true
  explode      := true
  deriving BEq

structure Backend where
  optimizeExpl := false
  deriving BEq

inductive Debug.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq

structure Debug where
  exitPoint : Debug.ExitPoint := .none
  vizPath   : Option String   := none
  deriving BEq

end Config
open Config

structure Config extends Encoding, Gen, Backend, Debug
