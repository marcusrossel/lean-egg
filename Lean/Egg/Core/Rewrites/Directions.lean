namespace Egg.Rewrite

inductive Direction where
  | forward
  | backward
  deriving Inhabited

def Direction.merge : Direction → Direction → Direction
  | .forward, .forward  | .backward, .backward => .forward
  | .forward, .backward | .backward, .forward  => .backward

inductive Directions where
  | none
  | forward
  | backward
  | both

namespace Directions

instance : ToString Directions where
  toString
    | .none     => "none"
    | .forward  => "forward"
    | .backward => "backward"
    | .both     => "both"

-- The directions for which a given set is a superset of the other.
def satisfyingSuperset [BEq α] (lhs rhs : Array α) : Directions :=
  let rSupL := lhs.all rhs.contains
  let lSupR := rhs.all lhs.contains
  match lSupR, rSupL with
  | false, false => .none
  | false, true  => .backward
  | true,  false => .forward
  | true,  true  => .both

-- The greatest lower bound of two given directions where according to the lattice:
--        both
--       /    \
-- forward   backward
--      \     /
--       none
def meet : Directions → Directions → Directions
  | .both, d | d, .both                                             => d
  | .none, _ | _, .none | .backward, .forward | .forward, .backward => .none
  | .forward, .forward                                              => .forward
  | .backward, .backward                                            => .backward
