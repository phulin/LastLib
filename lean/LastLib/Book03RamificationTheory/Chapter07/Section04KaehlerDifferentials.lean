import LastLib.Book03RamificationTheory.Chapter07.Section03TheDerivativeFormula

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.4. Kähler differentials -/

/- SOURCE_ISSUE (7.4): The source says that residue separability alone lets
   Book 2 supply an integral generator.  Over an imperfect residue field, the
   integral monogenic conclusion also needs the henselian, finite-normalization,
   and defectless/monogenic hypotheses used by the local presentation theorem.
   The declarations below retain the explicit `hmono` certificate. -/

/-- A presentation-level form of `Ω[B⁄A] ≅ B/(f'(α)) dα`. -/
def chapter07MonogenicDifferentialPresentation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) : Prop :=
  ∃ e : KaehlerDifferential A B ≃ₗ[B]
      B ⧸ Ideal.span ({aeval α f.derivative} : Set B),
    e (KaehlerDifferential.D A B α) =
      Ideal.Quotient.mk (Ideal.span ({aeval α f.derivative} : Set B)) 1

@[simp] theorem chapter07MonogenicDifferentialPresentation_iff
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) :
    chapter07MonogenicDifferentialPresentation A B α f ↔
      ∃ e : KaehlerDifferential A B ≃ₗ[B]
          B ⧸ Ideal.span ({aeval α f.derivative} : Set B),
        e (KaehlerDifferential.D A B α) =
          Ideal.Quotient.mk (Ideal.span ({aeval α f.derivative} : Set B)) 1 :=
  Iff.rfl

theorem chapter07_kaehler_differential_monogenic_equiv
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07MonogenicDifferentialPresentation A B α f := by
  sorry

/- Mathlib's `KaehlerDifferential` is the canonical module; this is the
   computed zeroth Fitting ideal of the displayed one-generator presentation.
   The definition deliberately records the presentation rather than claiming
   a global Fitting-ideal API for arbitrary finite modules. -/
def chapter07ZerothFittingIdealOfMonogenicPresentation
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (α : B) (f : A[X]) : Ideal B :=
  Ideal.span ({aeval α f.derivative} : Set B)

theorem chapter07_fitting_ideal_of_monogenic_presentation_eq_different
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07ZerothFittingIdealOfMonogenicPresentation A B α f =
      chapter07DifferentIdeal A B := by
  symm
  exact chapter07_different_eq_derivative_ideal A B K L α f hmono

/-- The source's geometric slogan, made explicit as a vanishing statement. -/
theorem chapter07_unramified_monogenic_differentials_subsingleton
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hunit : chapter07DifferentIdeal A B = ⊤) :
    Subsingleton (KaehlerDifferential A B) := by
  sorry

theorem chapter07_differential_module_has_finite_length
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    IsFiniteLength B (KaehlerDifferential A B) := by
  sorry

theorem chapter07_different_exponent_eq_differential_length
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mB : Ideal B) (d : ℕ) (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hD : chapter07DifferentIdeal A B = mB ^ d) :
    Module.length B (KaehlerDifferential A B) = d := by
  sorry

/- This interface records the hypothesis needed before identifying a trace
   different with a differential Fitting ideal. -/
def chapter07TraceAndDifferentialAgreement
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X]) : Prop :=
  chapter07MonogenicDifferentialPresentation A B α f ∧
    chapter07MonogenicPresentation A B K L α f

theorem chapter07_trace_differential_agreement_from_presentation
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hpresentation : chapter07TraceAndDifferentialAgreement A B K L α f) :
    chapter07ZerothFittingIdealOfMonogenicPresentation A B α f =
      chapter07DifferentIdeal A B := by
  exact chapter07_fitting_ideal_of_monogenic_presentation_eq_different
    A B K L α f hpresentation.2

end

end LastLib.Book03RamificationTheory.Chapter07
