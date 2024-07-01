import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a :=
  by rw [eq_inv_of_mul_eq_one_left h, one_div]
