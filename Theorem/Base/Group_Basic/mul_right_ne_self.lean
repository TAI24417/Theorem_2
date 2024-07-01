import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_right_eq_self


open Function

universe u

variable {α β G : Type*}



variable {M : Type u} [LeftCancelMonoid M] {a b : M}

theorem mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 := mul_right_eq_self.not
