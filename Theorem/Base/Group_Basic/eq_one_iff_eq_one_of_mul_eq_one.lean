import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases


open Function

universe u

variable {α β G : Type*}
variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)
#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_one
#align eq_zero_iff_eq_zero_of_add_eq_zero eq_zero_iff_eq_zero_of_add_eq_zero
