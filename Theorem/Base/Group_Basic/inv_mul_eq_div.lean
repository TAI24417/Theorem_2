import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
#align inv_mul_eq_div inv_mul_eq_div
#align neg_add_eq_sub neg_add_eq_sub