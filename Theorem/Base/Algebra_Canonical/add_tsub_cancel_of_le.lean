import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs

#align_import algebra.order.sub.canonical from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"


variable {α : Type*}



variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine' le_antisymm _ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  exact add_le_add_left add_tsub_le_left a
