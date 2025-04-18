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

-- IMPORTANT: The C interface to egg depends on the order of these constructors.
inductive Directions where
  | none
  | forward
  | backward
  | both
  deriving Inhabited, BEq, Hashable

namespace Directions

def isNone : Directions → Bool
  | none => true
  | _    => false

def isBoth : Directions → Bool
  | both => true
  | _    => false

def contains : Directions → Direction → Bool
  | both, _ | forward, .forward | backward, .backward => true
  | _, _                                              => false

def without : Directions → Directions → Directions
  | d, none => d
  | _, both | forward, forward | backward, backward | none, _ => none
  | both, forward | backward, forward  => backward
  | both, backward | forward, backward => forward

-- The directions for which a given set is a superset of the other.
def satisfyingSuperset (lhs rhs : RBTree α cmp) : Directions :=
  match rhs.subset lhs, lhs.subset rhs with
  | false, false => none
  | false, true  => backward
  | true,  false => forward
  | true,  true  => both

-- The greatest lower bound of two given directions according to the lattice:
--        both
--       /    \
-- forward   backward
--      \     /
--       none
def meet : Directions → Directions → Directions
  | both, d | d, both                                         => d
  | none, _ | _, none | backward, forward | forward, backward => none
  | forward, forward                                          => forward
  | backward, backward                                        => backward
