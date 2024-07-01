import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Theorem.Base.Algebra_Canonical.add_tsub_cancel_iff_le


variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}


theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl
