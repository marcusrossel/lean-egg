import Egg

set_option egg.eraseLambdaDomains true

set_option egg.eraseLambdaDomains false in
example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg [Nat.zero_add]

set_option egg.eraseLambdaDomains false in
example : (fun x => x) = (fun x => 0 + x) := by
  egg [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + x) := by
  egg [Nat.zero_add]

-- BUG: The rewrite is actually bidirectional, but the domain is the only reference to the mvar for
--      `α` on the rhs.
variable (h : ∀ α : Type, (fun (_ : List α) => 0) = (fun _ => ([] : List α).length))
example : True = True := by
  sorry -- egg [h]
