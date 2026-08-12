import LastLib.Book03RamificationTheory.Chapter07.Section01MeasuringTheDefectOfIntegralTraceDuality
import LastLib.Book03RamificationTheory.Chapter07.Section02UnramifiednessAndTheDifferent
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section02CharacteristicPolynomialsAndIntegralRestriction
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section06TracePairingsAndSeparability
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section08NormsOfIdealsAndDeterminants
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

namespace LastLib.Book03RamificationTheory.Chapter08

noncomputable section

open Ideal Matrix Polynomial
open scoped BigOperators Polynomial TensorProduct nonZeroDivisors

/-!
Shared interfaces for Chapter 8.  The source chapter uses the trace dual and
the different as its intrinsic upstairs objects.  These wrappers keep that
book-facing vocabulary while retaining Mathlib's canonical lattices and
fractional ideals underneath.
-/

/-- The integral trace dual `B^∨` as a `B`-submodule of `L`. -/
def chapter08TraceDualLattice
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Submodule B L :=
  Submodule.traceDual A K (1 : Submodule B L)

/-- Pointwise trace-dual membership, with the coefficient ring made explicit. -/
def chapter08TraceDualSet
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Set L :=
  {x | ∀ y : B,
    Algebra.trace K L (x * algebraMap B L y) ∈ Set.range (algebraMap A K)}

@[simp]
theorem chapter08_mem_traceDualLattice_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (x : L) :
    x ∈ chapter08TraceDualLattice A B K L ↔
      ∀ y : B,
        Algebra.trace K L (x * algebraMap B L y) ∈ Set.range (algebraMap A K) := by
  change x ∈ Submodule.traceDual A K (1 : Submodule B L) ↔ _
  constructor
  · intro hx y
    have hx' := (Submodule.mem_traceDual.mp hx)
      (algebraMap B L y) (by simp [Submodule.one_eq_range])
    simpa [Algebra.traceForm_apply] using hx'
  · intro hx
    apply Submodule.mem_traceDual.mpr
    intro b hb
    rcases (show ∃ y : B, algebraMap B L y = b by
      simpa [Submodule.one_eq_range] using hb) with ⟨y, rfl⟩
    simpa [Algebra.traceForm_apply] using hx y

@[simp]
theorem chapter08_traceDualLattice_coe_eq_set
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] :
    (chapter08TraceDualLattice A B K L : Set L) =
      chapter08TraceDualSet A B K L := by
  ext x
  exact chapter08_mem_traceDualLattice_iff A B K L x

@[simp]
theorem chapter08_mem_traceDualSet_iff_exists
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (x : L) :
    x ∈ chapter08TraceDualSet A B K L ↔
      ∀ y : B, ∃ a : A,
        algebraMap A K a = Algebra.trace K L (x * algebraMap B L y) := by
  rfl

/-- The fractional-ideal realization of the codifferent. -/
noncomputable def chapter08CodifferentFractionalIdeal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    FractionalIdeal B⁰ L :=
  FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)

/-- The different as the inverse of the codifferent fractional ideal. -/
noncomputable def chapter08DifferentFractionalIdeal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    FractionalIdeal B⁰ L :=
  (chapter08CodifferentFractionalIdeal A B K L)⁻¹

/-- The different ideal in the integral closure. -/
def chapter08DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

theorem chapter08_different_fractional_is_inverse_codifferent
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    chapter08DifferentFractionalIdeal A B K L =
      (chapter08CodifferentFractionalIdeal A B K L)⁻¹ := by
  rfl

/-- The unique exponent of a specified ideal power, when it exists. -/
noncomputable def chapter08UniqueIdealExponent
    {R : Type*} [CommRing R] (m I : Ideal R)
    (h : ∃! d : ℕ, I = m ^ d) : ℕ :=
  Classical.choose h

theorem chapter08UniqueIdealExponent_spec
    {R : Type*} [CommRing R] (m I : Ideal R)
    (h : ∃! d : ℕ, I = m ^ d) :
    I = m ^ chapter08UniqueIdealExponent m I h := by
  exact (Classical.choose_spec h).1

/- A pointwise form of the Hom-identification used in the trace-dual proof. -/
def chapter08TraceHomTowerCompatibility
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] : Prop :=
  ∀ x : C, ∀ b : B,
    Algebra.trace A C (x * algebraMap B C b) =
      Algebra.trace A B (Algebra.trace B C x * b)

/- The right B-action on Hom_A(B,A) is written explicitly so that the
   displayed Hom-identification in §8.3 does not depend on a noncanonical
   global module instance for a dual. -/
def chapter08DualRightAction
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (φ : B →ₗ[A] A) : B →ₗ[A] A :=
  φ.comp (LinearMap.mulRight A b)

def chapter08TraceHomBLinear
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (φ : C →ₗ[A] (B →ₗ[A] A)) : Prop :=
  ∀ b x, φ (b • x) = chapter08DualRightAction A B b (φ x)

/- A concrete, reusable record for the natural Hom_A/Hom_B equivalence. -/
structure Chapter08TraceHomTowerEquivalence
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] where
  forward : (C →ₗ[A] A) →
    {φ : C →ₗ[A] (B →ₗ[A] A) // chapter08TraceHomBLinear A B C φ}
  inverse :
    {φ : C →ₗ[A] (B →ₗ[A] A) // chapter08TraceHomBLinear A B C φ} →
      (C →ₗ[A] A)
  inverse_forward : ∀ f, inverse (forward f) = f
  forward_inverse : ∀ f, forward (inverse f) = f

end

end LastLib.Book03RamificationTheory.Chapter08
