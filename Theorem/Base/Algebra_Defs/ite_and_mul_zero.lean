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

theorem ite_and_mul_zero {α : Type*} [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q]
    (a b : α) : ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]
