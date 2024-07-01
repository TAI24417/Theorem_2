import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Theorem.Base.Algebra_Defs.Defs
import Theorem.Base.Algebra_Defs.mul_sub_left_distrib
import Theorem.Base.Algebra_Defs.neg_mul_eq_neg_mul

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

variable [NonUnitalNonAssocRing α]

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c


alias sub_mul := mul_sub_right_distrib
#align sub_mul sub_mul

#noalign mul_add_eq_mul_add_iff_sub_mul_add_eq
#noalign sub_mul_add_eq_of_mul_add_eq_mul_add
