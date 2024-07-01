import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_pos_iff_not_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_le
