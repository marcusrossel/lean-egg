import PowerCalc.Examples.PolynomialsPerformance.Basic


set_option maxHeartbeats 10000000
theorem freshmans_dream
  (comm_add : forall a b : R,  a + b = b + a)
  (comm_mul:  forall a b : R, a * b = b * a)
  (add_assoc: forall a b c : R, a + (b + c) = (a + b) + c)
  (mul_assoc: forall a b c : R, a * (b * c) = (a * b) * c)
  (sub_canon: forall a b : R, (a - b)  = a + (R.neg b))
  (neg_add : forall a : R , a + (R.neg a) = zero)
  (div_canon : forall a b : R, (a / b) = a * (R.inv b))
  (zero_add: forall a : R, a + zero = a )
  (zero_mul: forall a : R, a * zero = zero)
  (one_mul: forall a : R,  a * one = a)
  (distribute: forall a b c : R, a * (b + c)  = (a * b) + (a * c))
  (pow_one: forall a : R, a^1 = a )
  (pow_2: forall a : R, a*a = a^2 )
  (char_2 : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^2 = (x^2) + y^(2)   := 
  by calc (x + y)^2 = (x + y) * (x + y) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_2, char_2]
                    _ = (x * (x + y) + y * (x + y)) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_2, char_2]
                    _ = (x^2 + x * y + y * x + y^2) := by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_2, char_2]
                    _ = (x^2) + (y^2) :=  by simp [comm_add , comm_mul, add_assoc, mul_assoc, sub_canon, neg_add , div_canon , zero_add, zero_mul, one_mul, distribute, pow_one, pow_2, char_2]
   