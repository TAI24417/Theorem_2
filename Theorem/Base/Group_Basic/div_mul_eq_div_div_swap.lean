import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv


theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b :=
  by simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]
