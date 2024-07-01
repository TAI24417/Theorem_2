import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.lt_of_tsub_lt_tsub_left_of_le

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]


theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)] (hca : c ≤ a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h
