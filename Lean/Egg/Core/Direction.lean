import Lean
open Lean

namespace Egg

inductive Direction where
  | forward
  | backward
  deriving Inhabited, BEq, Hashable

def Direction.description : Direction → String
  | forward  => "→"
  | backward => "←"

def Direction.merge : Direction → Direction → Direction
  | forward, forward  | backward, backward => forward
  | forward, backward | backward, forward  => backward
