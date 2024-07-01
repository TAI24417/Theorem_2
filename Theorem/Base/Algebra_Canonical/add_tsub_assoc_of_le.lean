import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.eq_tsub_iff_add_eq_of_le

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c ≤ b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]
