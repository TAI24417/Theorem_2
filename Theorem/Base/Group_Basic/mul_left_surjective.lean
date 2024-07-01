import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [Group G] {a b c d : G}

theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) :=
  fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩
