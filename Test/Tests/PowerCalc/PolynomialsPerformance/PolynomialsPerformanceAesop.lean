import aesop

def R: Type := sorry
def add: R → R → R := sorry
def sub: R → R → R := sorry
def mul: R → R → R := sorry
def pow: R → R → R := sorry
def zero : R := sorry
def one: R := sorry
def two : R := sorry
def three : R := sorry
def four : R := sorry
def inv : R → R := sorry
def neg : R → R := sorry
def comm_add : forall a b : R,  (add a b)        = (add b a) := sorry
@[aesop unsafe 50%]
macro "comm_add_rw" : tactic => `(tactic| rw [comm_add])

@[aesop unsafe 50% apply]
def comm_mul:  forall a b : R, (mul a b)        = (mul b a) := sorry
def assoc_add: forall a b c : R, (add a (add b c)) = (add (add a b) c) := sorry
def assoc_mul: forall a b c : R, (mul a (mul b c)) = (mul (mul a b) c) := sorry
@[aesop unsafe 50% apply]
def add_assoc: forall a b c : R, (add (add a b) c) = (add a (add b c)) := sorry
def mul_assoc: forall a b c : R, (mul (mul a b) c) = (mul a (mul b c)) := sorry
def sub_canon: forall a b : R, (sub a b) = (add a (mul (neg one) b)) := sorry
def canon_sub: forall a b : R, (add a (mul (neg one) b)) = (sub a b)  := sorry
@[aesop unsafe 50% apply]
def zero_add: forall a : R, (add a zero) = a := sorry
def zero_mul: forall a : R, (mul a zero) = zero := sorry
def one_mul: forall a : R,   (mul a one) = a := sorry
def add_zero: forall a : R,  a = (add a zero) := sorry
def mul_one: forall a : R,   a = (mul a one) := sorry
def cancel_sub: forall a : R,  (sub a a) = zero := sorry
@[aesop unsafe 50% apply]
def distribute: forall a b c : R, (mul a (add b c))        = (add (mul a b) (mul a c)) := sorry
def factor    : forall a b c : R, (add (mul a b) (mul a c)) = (mul a (add b c)) := sorry
def pow_mul: forall a b c : R, (mul (pow a b) (pow a c)) = (pow a (add b c)) := sorry
def pow_one: forall a : R, (pow a one) = a := sorry
@[aesop unsafe 50% apply]
def pow_two: forall a : R, (pow a two) = (mul a a) := sorry
def pow_three: forall a : R, (pow a three) = (mul a (pow a two)) := sorry
def pow_four: forall a : R, (pow a four) = (mul (pow a two) (pow a two)) := sorry
def one_pow: forall a : R, a = (pow a one) := sorry
def two_pow: forall a : R, (mul a a) = (pow a two) := sorry
def three_pow: forall a : R, (mul a (pow a two)) = (pow a three) := sorry
def four_pow: forall a : R, (mul (pow a two) (pow a two)) = (pow a four) := sorry
def two_add : forall a : R, (add a a) = (mul two a) := sorry
def add_two : forall a : R, (mul two a) = (add a a) := sorry
@[aesop unsafe 50% apply]
def char_two : forall a : R, (add a a) = zero := sorry

theorem freshmans_dream (x y : R)
  : (pow (add x y) two) = (add (pow x two) (pow y two)) := by
  calc (pow (add x y) two) = (mul (add x y) (add x y)) := by rw [pow_two]
                         _ = add (mul (add x y) x) (mul (add x y) y) := by rw [distribute]
                         _ = add (mul x (add x y)) (mul (add x y) y) := by rw [comm_mul]
                         _ = add (add (mul x x) (mul x y)) (mul (add x y) y) := by rw [distribute]
                         _ = add (add (pow x two) (mul x y)) (mul (add x y) y) := by rw [pow_two]
                         _ = add (add (pow x two) (mul x y)) (mul y (add x y)) := by rw [comm_mul y _]
                         _ = add (add (pow x two) (mul x y)) (add (mul y x) (mul y y)) := by rw [distribute]
                         _ = add (add (pow x two) (mul x y)) (add (mul y x) (pow y two)) := by rw [pow_two y]
                         _ = add (add (pow x two) (mul x y)) (add (mul x y) (pow y two)) := by rw [comm_mul y x]
                         _ = add (pow x two) (add (mul x y) (add (mul x y) (pow y two))) := by rw [add_assoc]
                         _ = add (pow x two) (add (add (mul x y) (mul x y)) (pow y two)) := by rw [add_assoc]
                         _ = add (pow x two) (add zero (pow y two)) := by rw [char_two]
                         _ = add (pow x two) (add (pow y two) zero) := by rw [comm_add zero]
                         _ = add (pow x two) (pow y two) := by rw [zero_add]

set_option trace.aesop true
theorem freshmans_dream_aesop (x y : R)
  : (pow (add x y) two) = (add (pow x two) (pow y two)) := by
  aesop


