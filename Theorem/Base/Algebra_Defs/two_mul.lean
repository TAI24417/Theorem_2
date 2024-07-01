import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.right_distrib


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [NonAssocSemiring α]

theorem two_mul (n : α) : 2 * n = n + n :=
  (congrArg₂ _ one_add_one_eq_two.symm rfl).trans <| (right_distrib 1 1 n).trans (by rw [one_mul])
