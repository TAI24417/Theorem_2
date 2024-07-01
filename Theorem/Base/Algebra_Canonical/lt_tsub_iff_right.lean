import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Basic

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable


protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩



end AddLECancellable
