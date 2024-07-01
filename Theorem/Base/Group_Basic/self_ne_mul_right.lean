import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.self_eq_mul_right


open Function

universe u

variable {α β G : Type*}



variable {M : Type u} [LeftCancelMonoid M] {a b : M}

theorem self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 := self_eq_mul_right.not
