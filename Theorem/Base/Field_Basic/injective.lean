import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Ring.Commute
import Theorem.Base.Field_Basic.Commute_div_sub_div

#align_import algebra.field.basic from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type*}

namespace RingHom

protected theorem injective [DivisionRing α] [Semiring β] [Nontrivial β] (f : α →+* β) :
    Injective f :=
  (injective_iff_map_eq_zero f).2 fun _ ↦ (map_eq_zero f).1

end RingHom
