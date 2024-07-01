import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_lt_iff_left


variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc
