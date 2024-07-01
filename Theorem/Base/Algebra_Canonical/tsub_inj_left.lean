import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_left_inj

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) : b - a = c - a → b = c :=
  (tsub_left_inj h₁ h₂).1
