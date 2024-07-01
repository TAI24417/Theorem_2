import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_min

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  apply min_le_left
