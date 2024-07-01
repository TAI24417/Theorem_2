import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.self_eq_mul_left


open Function

universe u

variable {α β G : Type*}



variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[to_additive]
theorem self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 := self_eq_mul_left.not
#align self_ne_mul_left self_ne_mul_left
#align self_ne_add_left self_ne_add_left
