import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_eq_one_iff_eq_inv
import Theorem.Base.Group_Basic.inv_inj

open Function

universe u

variable {α β G : Type*}

variable [Group G] {a b c d : G}

theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]
