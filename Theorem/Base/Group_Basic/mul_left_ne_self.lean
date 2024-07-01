import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_left_eq_self


open Function

universe u

variable {α β G : Type*}



variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[to_additive]
theorem mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 := mul_left_eq_self.not
