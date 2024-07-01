import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.left_distrib
import Theorem.Base.Algebra_Defs.two_mul


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
