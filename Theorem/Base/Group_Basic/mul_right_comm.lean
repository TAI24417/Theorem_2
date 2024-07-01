import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases


open Function

universe u

variable {α β G : Type*}
variable [CommSemigroup G]

@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc
#align mul_right_comm mul_right_comm
#align add_right_comm add_right_comm
