namespace Egg.Config

structure Normalization where
  betaReduceRws := true
  etaReduceRws  := true
  natReduceRws  := true
  deriving BEq

def Normalization.noReduce : Normalization where
  betaReduceRws := false
  etaReduceRws  := false
  natReduceRws  := false

structure Encoding extends Normalization where
  -- TODO: Currently, this option implicitly disables defeq rewrites as they can not handle shapes, yet.
  shapes := false
  deriving BEq

-- TODO: The slotted backend is currently not supported.
def Encoding.slotted (_ : Encoding) : Bool :=
  false

structure Gen where
  baskets       := (#[] : Array Lean.Name)
  builtins      := true
  structProjs   := true
  tcProjs       := true
  tcProjFusion  := false
  goalTypeSpec  := true
  groundEqs     := true
  derivedGuides := true
  explosion     := false
  deriving BEq

structure DefEq where
  natLit    := true
  eta       := true
  etaExpand := false
  beta      := true
  levels    := true

structure Backend where
  unionSemantics := true
  optimizeExpl   := true
  timeLimit      := 3
  nodeLimit      := 1000000000000000000
  iterLimit      := 1000000000000000000
  reporting      := false
  flattenReports := false
  deriving BEq

inductive Debug.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq, Inhabited

structure Debug where
  exitPoint  := Debug.ExitPoint.none
  proofFuel? := (none : Option Nat)
  vizPath    := (none : Option String)
  deriving BEq

structure _root_.Egg.Config extends Encoding, DefEq, Gen, Backend, Debug where
  retryWithShapes := false
  explLengthLimit := 200
  subgoals        := false

instance : Coe Encoding Normalization where
  coe := Encoding.toNormalization

instance : Coe Config Encoding where
  coe := toEncoding

instance : Coe Config Gen where
  coe := toGen
