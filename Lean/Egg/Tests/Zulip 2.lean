import Egg

-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/completing.20the.20proof.20somewhat.20automatically/with/520934553

variable {A B C D E F G : Prop}
variable (a : A → B → D) (b : C → A → F) (c_1 : F → A → G) (c : D → G → F → E)

example (ho : A) (h1 : B) (h2 : C) : E := by
  egg [*]
