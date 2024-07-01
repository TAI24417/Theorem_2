import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_eq_zero_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le <| zero_le a
