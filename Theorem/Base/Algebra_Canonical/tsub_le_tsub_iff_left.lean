import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.add_tsub_assoc_of_le
import Theorem.Base.Algebra_Canonical.le_tsub_iff_right


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := by
  refine' ⟨_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha


end AddLECancellable
