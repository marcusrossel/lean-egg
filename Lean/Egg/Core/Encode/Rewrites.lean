import Egg.Core.Encode.Basic
import Egg.Core.Rewrites.Basic
import Lean
open Lean

namespace Egg

structure Rewrite.Encoded where
  name : String
  lhs  : Expression
  rhs  : Expression
  dirs : Rewrite.Directions

def Rewrite.encode (cfg : Config.Encoding) (explode : MVars) (rw : Rewrite) : MetaM Encoded :=
  return {
    name := rw.src.description
    lhs  := ← Egg.encode rw.lhs rw.src cfg explode
    rhs  := ← Egg.encode rw.rhs rw.src cfg explode
    dirs := rw.dirs
  }

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (cfg : Config.Encoding) (explode : MVars) : MetaM Rewrites.Encoded :=
  rws.mapM (Rewrite.encode cfg explode)

namespace Encoded

def names (rws : Encoded) : Array String :=
  rws.map (·.name)

def lhss (rws : Encoded) : Array Expression :=
  rws.map (·.lhs)

def rhss (rws : Encoded) : Array Expression :=
  rws.map (·.rhs)

def dirs (rws : Encoded) : Array Rewrite.Directions :=
  rws.map (·.dirs)
