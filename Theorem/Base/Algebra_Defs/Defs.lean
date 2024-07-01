import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists

#align_import algebra.ring.defs from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to `Algebra.Group.Defs` and
`Algebra.Group.Basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `Distrib`: Typeclass for distributivity of multiplication over addition.
* `HasDistribNeg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `Units`.
* `(NonUnital)(NonAssoc)(Semi)Ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`Semiring`, `CommSemiring`, `Ring`, `CommRing`, domain, `IsDomain`, nonzero, units
-/

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `Distrib` class
-/


/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align distrib Distrib

/-- A typeclass stating that multiplication is left distributive over addition. -/
class LeftDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
#align left_distrib_class LeftDistribClass

/-- A typeclass stating that multiplication is right distributive over addition. -/
class RightDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align right_distrib_class RightDistribClass

-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type*) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩
#align distrib.left_distrib_class Distrib.leftDistribClass

-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type*) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩
#align distrib.right_distrib_class Distrib.rightDistribClass

/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
#align non_unital_non_assoc_semiring NonUnitalNonAssocSemiring

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
#align non_unital_semiring NonUnitalSemiring

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α
#align non_assoc_semiring NonAssocSemiring

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α
#align non_unital_non_assoc_ring NonUnitalNonAssocRing

-- We defer the instance `NonUnitalNonAssocRing.toHasDistribNeg` to `Algebra.Ring.Basic`
-- as it relies on the lemma `eq_neg_of_add_eq_zero_left`.
/-- An associative but not-necessarily unital ring. -/
class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α
#align non_unital_ring NonUnitalRing

/-- A unital but not-necessarily-associative ring. -/
class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α
#align non_assoc_ring NonAssocRing

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
#align semiring Semiring

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
#align ring Ring


class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α
#align non_unital_comm_semiring NonUnitalCommSemiring

class CommSemiring (R : Type u) extends Semiring R, CommMonoid R
#align comm_semiring CommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
#align comm_semiring.to_non_unital_comm_semiring CommSemiring.toNonUnitalCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { inferInstanceAs (CommMonoid α), inferInstanceAs (CommSemiring α) with }
#align comm_semiring.to_comm_monoid_with_zero CommSemiring.toCommMonoidWithZero


class HasDistribNeg (α : Type*) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)
#align has_distrib_neg HasDistribNeg


section Ring

variable [Ring α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with }
#align ring.to_non_unital_ring Ring.toNonUnitalRing

-- A (unital, associative) ring is a not-necessarily-associative ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with }
#align ring.to_non_assoc_ring Ring.toNonAssocRing

/- The instance from `Ring` to `Semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) : Semiring α :=
  { ‹Ring α› with }
#align ring.to_semiring Ring.toSemiring

end Ring

/-- A non-unital commutative ring is a `NonUnitalRing` with commutative multiplication. -/
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α
#align non_unital_comm_ring NonUnitalCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }
#align non_unital_comm_ring.to_non_unital_comm_semiring NonUnitalCommRing.toNonUnitalCommSemiring

class CommRing (α : Type u) extends Ring α, CommMonoid α
#align comm_ring CommRing

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }
#align comm_ring.to_comm_semiring CommRing.toCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }
#align comm_ring.to_non_unital_comm_ring CommRing.toNonUnitalCommRing

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toAddCommGroupWithOne [s : CommRing α] :
    AddCommGroupWithOne α :=
  { s with }

/-- A domain is a nontrivial semiring such multiplication by a non zero element is cancellative,
  on both sides. In other words, a nontrivial semiring `R` satisfying
  `∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
  `∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

  This is implemented as a mixin for `Semiring α`.
  To obtain an integral domain use `[CommRing α] [IsDomain α]`. -/
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop
#align is_domain IsDomain

/-!
Previously an import dependency on `Mathlib.Algebra.Group.Basic` had crept in.
In general, the `.Defs` files in the basic algebraic hierarchy should only depend on earlier `.Defs`
files, without importing `.Basic` theory development.

These `assert_not_exists` statements guard against this returning.
-/
assert_not_exists DivisionMonoid.toDivInvOneMonoid
assert_not_exists mul_rotate
