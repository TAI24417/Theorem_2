import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_div
import Theorem.Base.Group_Basic.mul_div_cancel''


open Function

universe u

variable {α β G : Type*}

variable [Group G] {a b c d : G}

theorem div_mul_cancel''' (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel'']
