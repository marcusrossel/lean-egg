import Lean
open Lean

namespace Egg

inductive Direction where
  | forward
  | backward
  deriving Inhabited, BEq, Hashable

namespace Direction

def description : Direction → String
  | forward  => "→"
  | backward => "←"

def opposite : Direction → Direction
  | forward  => backward
  | backward => forward

def merge : Direction → Direction → Direction
  | forward, forward  | backward, backward => forward
  | forward, backward | backward, forward  => backward
