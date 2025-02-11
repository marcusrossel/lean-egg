import Egg

-- works
example T x1 x2 : @Eq T x1 (@Prod.mk T T x1 x2).1 := by rfl

example (x1 x2 : α) : x1 = (x1,x2).1 := by rfl

example (x1 x2 : α) : x1 = (x1,x2).1 := by egg

set_option trace.egg true in
example (x1 x2 : α) : x1 = Prod.fst (Prod.mk x1 x2) := by egg

set_option pp.raw true in
#eval (1,2)

#reduce  Prod.fst (Prod.mk ?Prod.fst ?Prod.snd)

open Lean in
#eval show MetaM Unit from do
  let α ← mkFreshLMVarId
  let β ← mkFreshLMVarId
  let x ← mkFreshLMVarId
  let y ← mkFreshLMVarId
  let lhs ← mkAppN (mkConst `Prod.fst) #[mkAppN `Prod.mk #[mkMVar x, mkMVar y]]
  let rhs ← getConstInfo `rhs
  Lean.logInfo s!"{lhs.value!}"
  Lean.logInfo s!"{(← Lean.Meta.isDefEq lhs.value! rhs.value!)}"


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

set_option pp.raw true
#eval (1,2)
