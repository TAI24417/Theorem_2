import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_self



variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  cases' le_total a b with h h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]
