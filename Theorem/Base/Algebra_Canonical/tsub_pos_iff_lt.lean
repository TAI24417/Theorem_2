import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_pos_iff_not_le



variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]
