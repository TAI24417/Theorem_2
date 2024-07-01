import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [Group G] {a b c d : G}

theorem mul_div_cancel'' (a b : G) : a * b / b = a :=
  by rw [div_eq_mul_inv, mul_inv_cancel_right a b]
