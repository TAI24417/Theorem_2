import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.div_one


open Function

universe u

variable {α β G : Type*}
variable [DivInvOneMonoid G]



@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _
#align one_div_one one_div_one
#align zero_sub_zero zero_sub_zero
