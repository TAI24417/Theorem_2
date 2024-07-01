import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases


open Function

universe u

variable {α β G : Type*}
variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one
