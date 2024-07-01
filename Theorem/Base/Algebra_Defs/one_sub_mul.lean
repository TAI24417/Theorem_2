import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.mul_sub_right_distrib

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [NonAssocRing α]

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]
