import LastLib.Book03RamificationTheory.Chapter15.Section02ACalculationProtocol
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RepresentationTheory.Rep.Basic

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

open scoped BigOperators

/-! ## 15.3. Consequences for two-dimensional arithmetic -/

/-- The kernel of a finite-dimensional linear representation. -/
def chapter15RepresentationKernel
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Subgroup G :=
  MonoidHom.ker ρ

/-- A representation kernel is normal, so it defines a quotient Galois layer. -/
theorem chapter15_representation_kernel_normal
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    (chapter15RepresentationKernel ρ).Normal := by
  sorry

instance chapter15_representation_kernel_normal_instance
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    (chapter15RepresentationKernel ρ).Normal :=
  chapter15_representation_kernel_normal ρ

/-- The fixed field cut out by a representation of a finite Galois group. -/
def chapter15RepresentationFixedField
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    (ρ : Representation k (Gal(L / K)) V) : IntermediateField K L :=
  IntermediateField.fixedField (chapter15RepresentationKernel ρ)

/-- The finite quotient seen by a representation is the Galois group of its fixed field. -/
theorem chapter15_representation_quotient_is_fixed_field_galois_group
    {k K L V : Type*} [Semiring k] [Field K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module k V]
    [FiniteDimensional K L] [IsGalois K L]
    (ρ : Representation k (Gal(L / K)) V) :
    Nonempty
      ((Gal(L / K) ⧸ chapter15RepresentationKernel ρ) ≃*
        Gal(chapter15RepresentationFixedField ρ / K)) := by
  sorry

/-- A finite-image representation together with the finite quotient through which it factors. -/
def chapter15FactorsThroughFiniteQuotient
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  ∃ (Q : Type*) (hQ : Group Q) (hQfinite : Finite Q),
    (letI : Group Q := hQ
     letI : Finite Q := hQfinite
     ∃ (π : G →* Q) (ρQ : Representation k Q V), ρ = ρQ.comp π)

/-- The finite quotient is the only Galois layer needed by a finite representation. -/
theorem chapter15_finite_image_representation_uses_finite_galois_layer
    {k G V : Type*} [Semiring k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    chapter15FactorsThroughFiniteQuotient ρ := by
  sorry

/-- In dimension two, the tame fixed-space codimension is exactly `0`, `1`, or `2`. -/
theorem chapter15_two_dimensional_tame_codimension_cases
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Chapter15LowerRamificationFiltration G)
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) :
    chapter15Codimension ρ (F.group 0) = 0 ∨
      chapter15Codimension ρ (F.group 0) = 1 ∨
      chapter15Codimension ρ (F.group 0) = 2 := by
  sorry

/-- The permutation module on a finite G-set, in the canonical group-algebra model. -/
def chapter15PermutationRepresentation
    (k G X : Type*) [Field k] [Group G] [MulAction G X] :
    Representation k G (MonoidAlgebra k X) :=
  (Rep.ofMulAction k G X).ρ

/-- The permutation conductor is the discriminant exponent of the corresponding field extension. -/
theorem chapter15_permutation_conductor_recovers_discriminant
    {A B G k : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Field k] (p : Ideal A) [p.IsPrime] [Finite (p.primesOver B)]
    [FiniteDimensional k (MonoidAlgebra k (p.primesOver B))]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (F : Chapter15LowerRamificationFiltration G)
    (hbranches : (p.primesOver B).ncard = 1) :
    chapter15ArtinConductor F
        (chapter15PermutationRepresentation k G (p.primesOver B)) =
      (chapter15DiscriminantExponent A B p : ℚ) := by
  sorry

/-- A field discriminant is an ideal-valued invariant, distinct in kind from a model discriminant. -/
abbrev Chapter15FieldDiscriminant (A : Type*) [Semiring A] := Ideal A

/-- The discriminant of a chosen Weierstrass model is coefficient-valued. -/
abbrev Chapter15WeierstrassDiscriminant (R : Type*) := R

end

end LastLib.Book03RamificationTheory.Chapter15
