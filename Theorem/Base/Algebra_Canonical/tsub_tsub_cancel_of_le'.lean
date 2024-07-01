import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_tsub_cancel_of_le

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]


theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h
