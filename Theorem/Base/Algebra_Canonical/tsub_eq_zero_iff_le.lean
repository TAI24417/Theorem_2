import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.add_tsub_cancel_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


@[simp]
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le
#align tsub_eq_zero_of_le tsub_eq_zero_of_le

attribute [simp] tsub_eq_zero_of_le
