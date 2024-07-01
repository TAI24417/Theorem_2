import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Basic
import Theorem.Base.Algebra_Canonical.tsub_lt_self


variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine'
    ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false
