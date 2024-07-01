import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_eq_zero_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne.def, tsub_eq_zero_iff_le]
