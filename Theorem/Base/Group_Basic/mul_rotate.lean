import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_left_comm

open Function

universe u

variable {α β G : Type*}
variable [CommSemigroup G]

@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a :=
  by simp only [mul_left_comm, mul_comm]
