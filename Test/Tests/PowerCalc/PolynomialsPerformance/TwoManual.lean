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
  (pow_2: forall a : R, a*a = a^2)
  (char_2 : forall a : R, a + a = zero )
  (x y : R)
  : (x + y)^2 = (x^2) + y^(2)   := by
  calc (x + y)^2 = (x + y) * (x + y) := by rw [← pow_2]
                 _ = ((x + y) * x) + ((x + y) * y) := by rw [distribute]
                 _ = (x * (x + y)) + ((x + y) * y) := by rw [comm_mul]
                 _ = ((x * x) + (x * y)) + ((x + y) * y) := by rw [distribute]
                 _ = ((x^2) + (x * y)) + ((x + y) * y) := by rw [pow_2]
                 _ = ((x^2) + (x * y)) + (y * (x + y)) := by rw [comm_mul y _]
                 _ = ((x^2) + (x * y)) + ((y * x) + (y * y)) := by rw [distribute]
                 _ = ((x^2) + (x * y)) + ((y * x) + (y^2)) := by rw [pow_2 y]
                 _ = ((x^2) + (x * y)) + ((x * y) + (y^2)) := by rw [comm_mul y x]
                 _ = (x^2) + ((x * y) + ((x * y) + (y^2))) := by rw [add_assoc (x^2)]
                 _ = (x^2) + (((x * y) + (x * y)) + (y^2)) := by rw [add_assoc (x * y)]
                 _ = (x^2) + (zero + (y^2)) := by rw [char_2]
                 _ = (x^2) + ((y^2) + zero) := by rw [comm_add zero]
                 _ = (x^2) + (y^2) := by rw [zero_add]
