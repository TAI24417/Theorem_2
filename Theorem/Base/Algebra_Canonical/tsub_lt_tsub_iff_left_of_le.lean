import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Basic
import Theorem.Base.Algebra_Canonical.tsub_le_tsub_iff_left


variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

namespace AddLECancellable

protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b ≤ a) : a - b < a - c ↔ c < b :=
  lt_iff_lt_of_le_iff_le <| ha.tsub_le_tsub_iff_left hb h
