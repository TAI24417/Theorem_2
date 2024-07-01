import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_eq_one_div


open Function

universe u

variable {α β G : Type*}

variable [DivInvMonoid G] {a b c : G}

theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm
