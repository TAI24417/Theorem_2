import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Ring.Commute
import Theorem.Base.Field_Basic.same_add_div

#align_import algebra.field.basic from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type*}

section DivisionSemiring

variable [DivisionSemiring α] {a b c d : α}

theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm
