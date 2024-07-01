import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.tsub_le_tsub_iff_left
import Theorem.Base.Algebra_Canonical.le_tsub_iff_right


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]

end AddLECancellable
