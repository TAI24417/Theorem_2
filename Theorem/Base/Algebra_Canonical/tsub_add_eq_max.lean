import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_lt_self

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]


theorem tsub_add_eq_max : a - b + b = max a b := by
  cases' le_total a b with h h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]
