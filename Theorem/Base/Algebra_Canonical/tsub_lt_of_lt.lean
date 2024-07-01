import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_le_self


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_lt tsub_le_self h
