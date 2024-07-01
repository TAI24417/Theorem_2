import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.bit1_add


open Function

universe u

variable {α β G : Type*}
set_option linter.deprecated false

variable {M : Type u} [AddCommSemigroup M]

theorem bit1_add' [One M] (a b : M) : bit1 (a + b) = bit1 a + bit0 b := by
  rw [add_comm, bit1_add, add_comm]
