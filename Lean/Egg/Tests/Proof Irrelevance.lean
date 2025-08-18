import Egg


example : @Eq (Fin 3) ⟨1, Nat.one_lt_succ_succ 1⟩ ⟨1, by omega⟩ := by
  rfl

example : @Eq (Fin 3) ⟨1, Nat.one_lt_succ_succ 1⟩ ⟨1, by omega⟩ := by
  egg

example  (l l' : List Nat) (a : Nat) :
       (a :: (l ++ l')).getLast (List.cons_ne_nil a _) =  ((a :: l) ++ l').getLast (List.cons_ne_nil a _) :=
         by egg [List.append]
