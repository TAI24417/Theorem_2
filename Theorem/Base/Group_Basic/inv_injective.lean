import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_involutive


open Function

universe u

variable {α β G : Type*}

variable [InvolutiveInv G] {a b : G}

@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective
#align inv_injective inv_injective
#align neg_injective neg_injective
