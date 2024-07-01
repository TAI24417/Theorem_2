import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_eq_zero_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl
