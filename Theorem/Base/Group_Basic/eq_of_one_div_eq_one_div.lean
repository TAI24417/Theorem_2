import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div_one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by sorry
  -- by rw [← one_div_one_div a, h, one_div_one_div]
