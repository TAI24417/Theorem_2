import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases


open Function

universe u

variable {α β G : Type*}
variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h:P <;> simp [h]
#align ite_one_mul ite_one_mul
#align ite_zero_add ite_zero_add
