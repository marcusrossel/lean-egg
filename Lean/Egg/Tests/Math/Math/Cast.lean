import Mathlib
import Egg

open Mathlib.Tactic.Zify in
attribute [egg zify] natCast_eq natCast_le natCast_lt natCast_ne natCast_dvd

open Mathlib.Tactic.Zify Nat Int in
attribute [egg zify] cast_sub_of_add_le cast_sub_of_lt natCast_inj natAbs_cast Int.cast_id
                natCast_pred_of_pos natCast_div natCast_mod natCast_dvd_natCast ofNat_isUnit
                WithZero.coe_div abs_natCast Int.cast_sub

open Mathlib.Tactic.Zify Nat Int in
#check Nat.cast_sub

example (a b : Nat) : (a = b) ↔ (a : Int) = (b : Int) := by
  sorry -- egg zify
