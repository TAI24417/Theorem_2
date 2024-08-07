import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.neg_mul
import Theorem.Base.Algebra_Defs.mul_neg


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [Mul α] [HasDistribNeg α]

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp
