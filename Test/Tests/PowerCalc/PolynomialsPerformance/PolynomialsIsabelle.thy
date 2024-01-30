section \<open>Examples from Commutative Algebra\<close>

theory PolynomialsIsabelle
  imports Main
begin


class ring = plus + minus + times + one + inverse + zero + uminus + power +
  assumes
      comm_add  : "a + b = b + a"
  and comm_mul  :  "a * b = b * a"
  and add_assoc : "a + (b + c) = (a + b) + c"
  and mul_assoc : "a * (b * c) = (a * b) * c"
  and sub_canon : "(a - b)  = a + (uminus b)"
  and neg_add   : "a + (uminus a) = 0"
  and div_canon : "(a / b) = a * (inverse b)"
  and zero_add  : "a + 0 = a"
  and zero_mul  : "a * 0 = 0"
  and one_mul   : "a * 1 = a"
  and distribute: "a * (b + c)  = (a * b) + (a * c)"
  and pow_one   : "a^1 = a"
  and pow_two   : "a*a = a^2"
  and pow_three : "a^2*a = a^3"
  and char_two  : " a + a = 0"

(*
  (x y : R)
  : (x + y)^2 = (x^2) + y^(2)   :=
  by calc := by ges
                    _ = := by ges
                    _ =  := by ges
                    _ =  :=  by ges
*)

theorem (in ring) freshmanns_dream_sledgehammer : "(x + y)^2 = x^2 + y^2"
proof 
  by (smt (verit) local.add_assoc local.char_two local.comm_mul local.distribute local.pow_one local.zero_add numeral_1_eq_Suc_0 numeral_2_eq_2 numerals(1) power.power.power_Suc)
  (* 
Failed to apply initial proof method:
goal (1 subgoal):
 1. (x + y)\<^sup>2 = x\<^sup>2 + y\<^sup>2
*)
  oops 

theorem (in ring) freshmanns_dream_guided : "(x + y)^2 = x^2 + y^2"
proof -
  have "(x + y)^2 = (x + y) * (x + y) "
  by (simp add: local.pow_two)
  also have "\<dots> = (x * (x + y) + y * (x + y)) "
  using local.comm_mul local.distribute by auto
  also have "\<dots> = (x^2 + x * y + y * x + y^2) "
  by (simp add: local.add_assoc local.distribute local.pow_two)
  also have "\<dots> =  (x^2) + (y^2)"
  by (metis local.add_assoc local.char_two local.comm_mul local.pow_two local.zero_add)
  finally show ?thesis .
qed


theorem (in ring) freshmanns_dream_3_guided : "(x + y)^3 = x^3 + x*y^2 + x^2*y + y^3"
proof -
  have "(x + y)^3 = (x+y)^2*(x + y)"
    by (simp add: local.pow_three)
  also have "\<dots> = (x^2 + y^2)* (x + y)"
    by (simp add: local.freshmanns_dream_guided)
  also have "\<dots> = x * ((x^2) + (y^2)) + y * ((x^2) + (y^2)) "
    by (metis (full_types) local.comm_mul local.distribute) 
  also have "\<dots> =  (x * x^2) + x*y^2 + y * x^2 + y*(y^2)"
    using local.add_assoc local.distribute by auto 
  also have "\<dots> = x^3 + x*y^2 + x^2*y + y^3"
    using local.comm_mul local.pow_three by presburger
  finally show ?thesis .
qed
