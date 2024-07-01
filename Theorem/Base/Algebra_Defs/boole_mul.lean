import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.mul_ite
import Theorem.Base.Algebra_Defs.ite_mul


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [NonAssocSemiring α]

attribute [simp] mul_ite ite_mul

theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp
