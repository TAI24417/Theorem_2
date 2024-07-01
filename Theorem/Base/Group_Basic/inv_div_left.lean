import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp
