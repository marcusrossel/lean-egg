namespace Egg.Config

structure Normalization where
  betaReduceRws := true
  etaReduceRws  := true
  natReduceRws  := true
  deriving BEq

def Normalization.noReduce : Normalization where
  betaReduceRws := true
  etaReduceRws  := true
  natReduceRws  := true

structure Encoding extends Normalization where
  eraseProofs := true
  deriving BEq

structure Gen where
  builtins      := true
  tagged?       := some `egg
  genTcProjRws  := true
  genTcSpecRws  := true
  genGoalTcSpec := true
  genNatLitRws  := true
  genEtaRw      := true
  genBetaRw     := true
  genLevelRws   := true
  deriving BEq

structure Backend where
  blockInvalidMatches := true
  shiftCapturedBVars  := true -- This option implies `blockInvalidMatches`.
  conditionSubgoals   := false
  optimizeExpl        := true
  timeLimit           := 3
  nodeLimit           := 1000000000000000000
  iterLimit           := 1000000000000000000
  reporting           := false
  flattenReports      := false
  deriving BEq

inductive Debug.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq, Inhabited

structure Debug where
  exitPoint           := Debug.ExitPoint.none
  vizPath             := (none : Option String)
  -- TODO: Debug tracing is currently disabled in Rust as it breaks builds on Linux.
  traceSubstitutions  := false
  traceBVarCorrection := false
  deriving BEq

structure _root_.Egg.Config extends Encoding, Gen, Backend, Debug

-- TODO: Why aren't these coercions automatic?

instance : Coe Encoding Normalization where
  coe := Encoding.toNormalization

instance : Coe Config Encoding where
  coe := toEncoding

instance : Coe Config Gen where
  coe := toGen
