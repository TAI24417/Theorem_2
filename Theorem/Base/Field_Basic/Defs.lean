import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Hom.Ring.Defs
import Mathlib.Algebra.Ring.Commute
import Theorem.Base.Field_Basic.Commute_div_sub_div

#align_import algebra.field.basic from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about division (semi)rings and (semi)fields

-/


open Function OrderDual Set

universe u

variable {α β K : Type*}


section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

/-- Constructs a `DivisionRing` structure on a `Ring` consisting only of units and 0. -/
noncomputable def divisionRingOfIsUnitOrEqZero [hR : Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }
#align division_ring_of_is_unit_or_eq_zero divisionRingOfIsUnitOrEqZero

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def fieldOfIsUnitOrEqZero [hR : CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }
#align field_of_is_unit_or_eq_zero fieldOfIsUnitOrEqZero

end NoncomputableDefs

-- See note [reducible non-instances]
/-- Pullback a `DivisionSemiring` along an injective function. -/
@[reducible]
protected def Function.Injective.divisionSemiring [DivisionSemiring β] [Zero α] [Mul α] [Add α]
    [One α] [Inv α] [Div α] [SMul ℕ α] [Pow α ℕ] [Pow α ℤ] [NatCast α] (f : α → β)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : DivisionSemiring α :=
  { hf.groupWithZero f zero one mul inv div npow zpow,
    hf.semiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.division_semiring Function.Injective.divisionSemiring

/-- Pullback a `DivisionSemiring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.divisionRing [DivisionRing K] {K'} [Zero K'] [One K'] [Add K']
    [Mul K'] [Neg K'] [Sub K'] [Inv K'] [Div K'] [SMul ℕ K'] [SMul ℤ K'] [SMul ℚ K']
    [Pow K' ℕ] [Pow K' ℤ] [NatCast K'] [IntCast K'] [RatCast K'] (f : K' → K) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
    DivisionRing K' :=
  { hf.groupWithZero f zero one mul inv div npow zpow,
    hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    ratCast := Rat.cast,
    ratCast_mk := fun a b h1 h2 ↦
      hf
        (by
          erw [rat_cast, mul, inv, int_cast, nat_cast]
          exact DivisionRing.ratCast_mk a b h1 h2),
    qsmul := (· • ·), qsmul_eq_mul' := fun a x ↦ hf (by erw [qsmul, mul, Rat.smul_def, rat_cast]) }
#align function.injective.division_ring Function.Injective.divisionRing

-- See note [reducible non-instances]
/-- Pullback a `Field` along an injective function. -/
@[reducible]
protected def Function.Injective.semifield [Semifield β] [Zero α] [Mul α] [Add α] [One α] [Inv α]
    [Div α] [SMul ℕ α] [Pow α ℕ] [Pow α ℤ] [NatCast α] (f : α → β) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semifield α :=
  { hf.commGroupWithZero f zero one mul inv div npow zpow,
    hf.commSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.semifield Function.Injective.semifield

/-- Pullback a `Field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.field [Field K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K']
    [One K'] [Inv K'] [Div K'] [SMul ℕ K'] [SMul ℤ K'] [SMul ℚ K'] [Pow K' ℕ] [Pow K' ℤ]
    [NatCast K'] [IntCast K'] [RatCast K'] (f : K' → K) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n) :
    Field K' :=
  { hf.commGroupWithZero f zero one mul inv div npow zpow,
    hf.commRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    ratCast := Rat.cast,
    ratCast_mk := fun a b h1 h2 ↦
      hf
        (by
          erw [rat_cast, mul, inv, int_cast, nat_cast]
          exact DivisionRing.ratCast_mk a b h1 h2),
    qsmul := (· • ·), qsmul_eq_mul' := fun a x ↦ hf (by erw [qsmul, mul, Rat.smul_def, rat_cast]) }
#align function.injective.field Function.Injective.field

/-! ### Order dual -/


instance [h : RatCast α] : RatCast αᵒᵈ :=
  h

instance [h : DivisionSemiring α] : DivisionSemiring αᵒᵈ :=
  h

instance [h : DivisionRing α] : DivisionRing αᵒᵈ :=
  h

instance [h : Semifield α] : Semifield αᵒᵈ :=
  h

instance [h : Field α] : Field αᵒᵈ :=
  h


/-! ### Lexicographic order -/

instance [h : RatCast α] : RatCast (Lex α) :=
  h

instance [h : DivisionSemiring α] : DivisionSemiring (Lex α) :=
  h

instance [h : DivisionRing α] : DivisionRing (Lex α) :=
  h

instance [h : Semifield α] : Semifield (Lex α) :=
  h

instance [h : Field α] : Field (Lex α) :=
  h
