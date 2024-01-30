import EggTactic

theorem freshmans_dream (R : Type) (add : R → R → R) (mul : R → R → R) (zero : R) 
  (x y : R) (pow : R → R → R)
  (pow_two: forall a : R, (pow a two) = (mul a a))
  (distribute: forall a b c : R, (mul a (add b c))        = (add (mul a b) (mul a c)))
  (comm_mul:  forall a b : R, (mul a b)        = (mul b a))
  (add_assoc: forall a b c : R, (add (add a b) c) = (add a (add b c)))
  (char_two : forall a : R, (add a a) = zero)
  (comm_add : forall a b : R,  (add a b)        = (add b a))
  (zero_add: forall a : R, (add a zero) = a)
  : (pow (add x y) two) = (add (pow x two) (pow y two)) :=
  by simp [pow_two, distribute, comm_mul, add_assoc, char_two, comm_add, zero_add] --simplify