import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Basic

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

end AddLECancellable
