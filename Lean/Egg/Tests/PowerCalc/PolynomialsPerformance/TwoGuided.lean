import PowerCalc.Examples.PolynomialsPerformance.Basic

open R in
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
  (pow_two: forall a : R, a*a = a^2)
  (char_two : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^2 = (x^2) + y^(2)   :=
  by calc (x + y)^2 = (x + y) * (x + y) := by ges
                    _ = (x * (x + y) + y * (x + y)) := by ges
                    _ = (x^2 + x * y + y * x + y^2) := by ges
                    _ = (x^2) + (y^2) :=  by ges
   