import Egg

variable (a : Nat)

-- TODO: This used to succeed prior to the `better-facts` PR.

set_option egg.timeLimit 10 in
set_option egg.reporting true in
example :
    a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t + u + v + w + x + y + z =
    z + y + x + w + v + u + t + s + r + q + p + o + n + m + l + k + j + i + h + g + f + e + d + c + b + a := by
  egg [Nat.add_comm, Nat.add_assoc]
