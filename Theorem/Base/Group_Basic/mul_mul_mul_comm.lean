import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_left_comm


open Function

universe u

variable {α β G : Type*}
variable [CommSemigroup G]

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) :=
  by simp only [mul_left_comm, mul_assoc]
