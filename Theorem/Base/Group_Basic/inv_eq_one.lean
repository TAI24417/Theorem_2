import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_injective
import Theorem.Base.Group_Basic.one_div
import Theorem.Base.Group_Basic.inv_div


open Function

universe u

variable {α β G : Type*}
variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv
variable {a b c}

@[to_additive (attr := simp)]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by sorry
  -- inv_injective.eq_iff' inv_one
