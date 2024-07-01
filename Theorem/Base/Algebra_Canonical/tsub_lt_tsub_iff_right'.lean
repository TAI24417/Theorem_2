import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_lt_tsub_iff_right

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h
