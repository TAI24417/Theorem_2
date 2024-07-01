import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.one_div


open Function

universe u

variable {α β G : Type*}

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

set_option linter.deprecated false

lemma bit0_neg [SubtractionMonoid α] (a : α) : bit0 (-a) = -bit0 a := (neg_add_rev _ _).symm
