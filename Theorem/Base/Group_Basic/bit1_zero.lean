import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.bit0_zero


open Function

universe u

variable {α β G : Type*}
set_option linter.deprecated false

variable {M : Type u} [AddMonoid M] {a b c : M}

theorem bit1_zero [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]
