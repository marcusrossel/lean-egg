import PowerCalc.Examples.PolynomialsPerformance.Basic

open R in
theorem freshmans_dream_pow3
  (two : R )
  (three : R )
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
  (pow_one: forall a : R, a^one = a )
  (pow_two: forall a : R, a*a = a^two)
  (pow_three: forall a : R, a^three = a*a^two)
  (char_two : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^three = x^three + x*y^two + x^two*y + y^three := by calc 
  (x + y)^three 
 _ = (x + y) * (x + y) * (x + y) := by ges3
 _ = (x + y) * (x * (x + y) + y * (x + y)) := by ges3
 _ = (x + y) * (x^two + x * y + y * x + y^two) := by ges3
 _ = (x + y) * (x^two + y^two) := by ges3
 _ = x * ((x^two) + (y^two)) + y * ((x^two) + (y^two)) :=  by ges3
 _ = (x * x^two) + x*y^two + y * x^two + y*(y^two) :=  by ges3
 _ = x^three + x*y^two + x^two*y + y^three := by ges3 