import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Cases
import Theorem.Base.Group_Basic.mul_left_eq_self


open Function

universe u

variable {α β G : Type*}

variable [InvolutiveInv G] {a b : G}

@[to_additive]
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  ⟨fun h => h ▸ (inv_inv a).symm, fun h => h.symm ▸ inv_inv b⟩
#align inv_eq_iff_eq_inv inv_eq_iff_eq_inv
#align neg_eq_iff_eq_neg neg_eq_iff_eq_neg
