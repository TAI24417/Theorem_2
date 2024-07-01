import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases


open Function

universe u

variable {α β G : Type*}

variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h:P <;> simp [h]
#align ite_mul_one ite_mul_one
#align ite_add_zero ite_add_zero
