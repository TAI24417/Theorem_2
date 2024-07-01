import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.inv_involutive


open Function

universe u

variable {α β G : Type*}

variable [InvolutiveInv G] {a b : G}

variable (G)

@[to_additive]
theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv
#align right_inverse_inv rightInverse_inv
#align right_inverse_neg rightInverse_neg
