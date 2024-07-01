import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.lt_tsub_iff_right_of_le

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]


theorem lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h
