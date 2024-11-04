import Egg

set_option egg.slotted true

def first (a : α) (_ : β) : α := a

theorem first_correct (a : α) (b : β) : first a b = a := rfl

-- BUG:
set_option trace.egg true in
set_option egg.builtins false in
set_option egg.optimizeExpl false in
example (f : α → α) : (fun x => (first f x) x) = f := by
  egg [first_correct]

example : (fun (z : α → α → α) x => (fun _y => z) x x) = (fun x => x) := by
  egg

/-
0: (fvar 97) = (fvar 97) by refl
1: (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3018)) = (fvar 98) by Some("#0")
2: (fvar 98) = (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3018)) by symmetry(1)
3: (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3018)) = (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3042)) by transitivity(1, 2)
4: (bvar $f3013) = (bvar $f3013) by refl
5: (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3461)) (bvar $f3015)) = (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3015)) (bvar $f3015)) by congruence(3, 4)
6: (λ $0 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3486)) (bvar $0))) = (λ $f3016 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3016)) (bvar $f3016))) by congruence(0, 5)
7: (λ $f3016 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3016)) (bvar $f3016))) = (λ $0 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3486)) (bvar $0))) by symmetry(6)

8: (λ $0 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3416)) (bvar $0))) = (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3494)) by Some("≡η")
                                                                                                                                                    ^^^^^^^

9: (λ $f3016 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3016)) (bvar $f3016))) = (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3497)) by transitivity(7, 8)
10: (λ $f3016 (fvar 97) (app (app (app (app (app (const "first" (param "u_1") (param "u_1")) (∀ $f3012 (fvar 97) (fvar 97))) (fvar 97)) (fvar 98)) (bvar $f3016)) (bvar $f3016))) = (fvar 98) by transitivity(9, 1)
-/
