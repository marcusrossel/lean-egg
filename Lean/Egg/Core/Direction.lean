import Lean
open Lean

namespace Egg

inductive Direction where
  | backward
  | forward
deriving Inhabited, BEq, Hashable, Ord

namespace Direction

def description : Direction → String
  | backward => "←"
  | forward  => "→"

def opposite : Direction → Direction
  | backward => forward
  | forward  => backward

def merge : Direction → Direction → Direction
  | backward, backward | forward, forward  => forward
  | backward, forward  | forward, backward => backward
