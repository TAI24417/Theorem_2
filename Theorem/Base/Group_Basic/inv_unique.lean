import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_mul_mul_comm


open Function

universe u

variable {α β G : Type*}
attribute [local simp] mul_assoc sub_eq_add_neg

section CommMonoid

variable {M : Type u} [CommMonoid M] {x y z : M}

@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz
#align inv_unique inv_unique
#align neg_unique neg_unique
