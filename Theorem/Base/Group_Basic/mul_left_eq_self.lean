import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_mul_mul_comm


open Function

universe u

variable {α β G : Type*}



variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_left_eq_self : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff
#align mul_left_eq_self mul_left_eq_self
#align add_left_eq_self add_left_eq_self
