import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c
#align right_distrib right_distrib

alias add_mul := right_distrib
#align add_mul add_mul
