import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.add_tsub_cancel_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}



theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le
#align tsub_add_cancel_iff_le tsub_add_cancel_iff_le
