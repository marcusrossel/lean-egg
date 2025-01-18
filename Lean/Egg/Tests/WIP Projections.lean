import Egg

-- works
example T x1 x2 : @Eq T x1 (@Prod.mk T T x1 x2).1 := by rfl

example (x1 x2 : α) : x1 = (x1,x2).1 := by rfl

example (x1 x2 : α) : x1 = (x1,x2).1 := by egg

example (x1 x2 : α) : x1 = Prod.fst (Prod.mk x1 x2) := by egg

example T x1 x2 : @Eq T x1 (@Prod.mk T T x1 x2).1 := by rfl

-- fails
example T x1 x2 val isLt :
  @Eq T
    (@List.get T x1
      (@Fin.mk (@List.length T x1) val
        isLt))
    (@List.get T x1
      (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val
         isLt)) := by egg

structure Foo where
  x : Nat
  y : Nat

example (m n : Nat) : { x := m, y := n : Foo}.x = m := by egg
