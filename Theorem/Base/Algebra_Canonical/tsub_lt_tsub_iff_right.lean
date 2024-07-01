import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Basic
import Theorem.Base.Algebra_Canonical.lt_tsub_iff_left
import Theorem.Base.Algebra_Canonical.add_tsub_cancel_of_le

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c ≤ a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]
