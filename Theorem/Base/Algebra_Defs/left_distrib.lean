import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function


theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c
#align left_distrib left_distrib

alias mul_add := left_distrib
#align mul_add mul_add
