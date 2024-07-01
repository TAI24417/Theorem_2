import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_involutive


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm
#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_right
#align eq_neg_of_add_eq_zero_right eq_neg_of_add_eq_zero_right
