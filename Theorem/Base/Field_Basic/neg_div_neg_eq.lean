import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Ring.Commute
import Theorem.Base.Field_Basic.div_neg_eq_neg_div

#align_import algebra.field.basic from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type*}

section DivisionSemiring

variable [DivisionMonoid K] [HasDistribNeg K] {a b : K}

theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]
