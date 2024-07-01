import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_injective


open Function

universe u

variable {α β G : Type*}

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff
#align inv_inj inv_inj
#align neg_inj neg_inj
