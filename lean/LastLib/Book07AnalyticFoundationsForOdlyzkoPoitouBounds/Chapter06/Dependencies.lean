import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.Support
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter NumberField
open scoped BigOperators ContDiff Topology

/-!
Shared interfaces for Chapter 6.  The completed-zeta facts are kept as a
small package because the preceding Chapter 4 draft is not present in this
checkout.  The book-facing definitions below nevertheless use the canonical
Mathlib number-field, discriminant, Gamma, and Laplace-transform objects.
-/

/-! ### Number-field and completion conventions -/

abbrev chapter06Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

noncomputable abbrev chapter06RealPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

noncomputable abbrev chapter06ComplexPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def chapter06Signature (K : Type*) [Field K] [NumberField K] : ℕ × ℕ :=
  (chapter06RealPlaces K, chapter06ComplexPlaces K)

noncomputable def chapter06AbsoluteDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

noncomputable def chapter06RootDiscriminant
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter06AbsoluteDiscriminant K ^ (chapter06Degree K : ℝ)⁻¹

def chapter06GammaReal (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

def chapter06GammaComplex (s : ℂ) : ℂ :=
  (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s

def chapter06CompletedDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter06AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
    chapter06GammaReal s ^ chapter06RealPlaces K *
    chapter06GammaComplex s ^ chapter06ComplexPlaces K *
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K s

def chapter06Xi
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * chapter06CompletedDedekindZeta K s

def chapter06LogDerivative (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  deriv f s / f s

def chapter06AnalyticConductor
    (K : Type*) [Field K] [NumberField K] (t : ℝ) : ℝ :=
  chapter06AbsoluteDiscriminant K * (|t| + 3) ^ chapter06Degree K

def chapter06VerticalLinePoint (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-! ### Test functions and the three archimedean integrals -/

abbrev Chapter06BasicallyAdmissible (F : ℝ → ℝ) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05BasicallyAdmissible F

def chapter06Phi (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform F s

def Chapter06SmoothCompactSupport (F : ℝ → ℝ) : Prop :=
  Function.Even F ∧ (ContDiff ℝ ∞ F) ∧ HasCompactSupport F

def chapter06A (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, F x * Real.cosh (x / 2)

def chapter06B (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))

def chapter06C (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))

def chapter06GammaConstant : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi)

def chapter06RealPlaceContribution (F : ℝ → ℝ) : ℝ :=
  chapter06GammaConstant + Real.pi / 2 - chapter06B F - chapter06C F

def chapter06ComplexPlaceContribution (F : ℝ → ℝ) : ℝ :=
  2 * chapter06GammaConstant - 2 * chapter06B F

/-! ### Prime powers -/

abbrev Chapter06PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Chapter03PrimeIdeal K

abbrev Chapter06PositiveExponent := {m : ℕ // 0 < m}

abbrev Chapter06PrimePower (K : Type*) [Field K] [NumberField K] :=
  Chapter06PrimeIdeal K × Chapter06PositiveExponent

def chapter06PrimeIdealNorm
    {K : Type*} [Field K] [NumberField K] (P : Chapter06PrimeIdeal K) : ℕ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03PrimeIdealNorm P

def chapter06PrimePowerTerm
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (q : Chapter06PrimePower K) : ℝ :=
  Real.log (chapter06PrimeIdealNorm q.1 : ℝ) *
    Real.rpow (chapter06PrimeIdealNorm q.1 : ℝ) (-((q.2.1 : ℝ) / 2)) *
    F ((q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ))

def chapter06PrimePowerSupport
    {K : Type*} [Field K] [NumberField K] (F : ℝ → ℝ) : Set (Chapter06PrimePower K) :=
  {q | chapter06PrimePowerTerm F q ≠ 0}

def chapter06SupportWithin (F : ℝ → ℝ) (T : ℝ) : Prop :=
  Function.support F ⊆ Set.Icc (-T) T

noncomputable def chapter06PrimeContribution
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℝ :=
  2 * ∑' q : Chapter06PrimePower K, chapter06PrimePowerTerm F q

/-! ### The zero spectrum and the missing Chapter 4 package -/

def chapter06NontrivialZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  chapter06Xi K ρ = 0

def chapter06SimplePoleWithResidue
    (f : ℂ → ℂ) (ρ r : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, DifferentiableAt ℂ g ρ ∧
    ∀ᶠ s in 𝓝[≠] ρ, f s = r / (s - ρ) + g s

structure Chapter06ZeroSpectrum
    (K : Type*) [Field K] [NumberField K] where
  support : Set ℂ
  multiplicity : ℂ → ℕ
  support_iff_multiplicity_ne_zero :
    ∀ ρ, ρ ∈ support ↔ multiplicity ρ ≠ 0
  support_iff_nontrivial_zero :
    ∀ ρ, ρ ∈ support ↔ chapter06NontrivialZero K ρ
  critical_strip :
    ∀ {ρ}, ρ ∈ support → 0 ≤ ρ.re ∧ ρ.re ≤ 1
  functional_equation_partner :
    ∀ {ρ}, ρ ∈ support ↔ 1 - ρ ∈ support
  conjugation_partner :
    ∀ {ρ}, ρ ∈ support ↔ star ρ ∈ support
  multiplicity_functional_equation_partner :
    ∀ ρ, multiplicity (1 - ρ) = multiplicity ρ
  multiplicity_conjugation_partner :
    ∀ ρ, multiplicity (star ρ) = multiplicity ρ
  log_derivative_simple_pole :
    ∀ {ρ}, ρ ∈ support →
      chapter06SimplePoleWithResidue
        (chapter06LogDerivative (chapter06Xi K)) ρ (multiplicity ρ : ℂ)
  locally_finite :
    ∀ T : ℝ, Set.Finite {ρ : ℂ | ρ ∈ support ∧ |ρ.im| < T}
  unit_band_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((Set.ncard {ρ : ℂ |
        ρ ∈ support ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1} : ℕ) : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3))

/-
DEPENDENCY_GUESS: Chapter 4 should provide this package.  Its zero field is
the completed-zeta zero multiset counted with multiplicity; the height field
records the order-one estimate and the inverse-polynomial choice of contour
heights used in §6.2.  It is deliberately an input interface, not an axiom
or a conclusion engineered from the explicit formula.
-/
structure Chapter06ContourHeightSequence
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (c : ℝ) where
  height : ℕ → ℝ
  tendsToInfinity : Tendsto height atTop atTop
  positive : ∀ j, 0 < height j
  separationExponent : ℕ
  separationConstant : ℝ
  separationConstant_pos : 0 < separationConstant
  avoids_zero_ordinates :
    ∀ (j : ℕ) (ρ : ℂ), ρ ∈ Z.support →
      separationConstant /
          Real.rpow (height j + 3) (separationExponent : ℝ) ≤
        |height j - ρ.im|
  logDerivativeBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (σ : ℝ),
      1 - c ≤ σ → σ ≤ c →
      ‖chapter06LogDerivative (chapter06Xi K)
          (chapter06VerticalLinePoint σ (height j))‖ ≤
        C * (Real.log (chapter06AnalyticConductor K (height j))) ^ 2 ∧
      ‖chapter06LogDerivative (chapter06Xi K)
          (chapter06VerticalLinePoint σ (-height j))‖ ≤
        C * (Real.log (chapter06AnalyticConductor K (height j))) ^ 2

structure Chapter06ZetaAnalyticPackage
    (K : Type*) [Field K] [NumberField K] where
  xi_entire : Differentiable ℂ (chapter06Xi K)
  functional_equation : ∀ s : ℂ, chapter06Xi K s = chapter06Xi K (1 - s)
  conjugation_symmetry : ∀ s : ℂ,
    chapter06Xi K (star s) = star (chapter06Xi K s)
  zeros : Chapter06ZeroSpectrum K
  contour_heights : ∀ c : ℝ, 1 < c →
    Chapter06ContourHeightSequence K zeros c

def chapter06ZeroCountingFunction
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | ρ ∈ Z.support ∧ |ρ.im| ≤ T}

def chapter06ZeroBandCount
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ |
    ρ ∈ Z.support ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1}

/-! ### Symmetric zero sums -/

def chapter06ZeroWindow
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ Z.support ∧ |ρ.im| < T}

noncomputable def chapter06ZeroWindowFinset
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (T : ℝ) : Finset ℂ :=
  (Z.locally_finite T).toFinset

def chapter06ZeroSummand
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (ρ : ℂ) : ℂ :=
  (Z.multiplicity ρ : ℂ) * chapter06Phi F ρ

noncomputable def chapter06SymmetricZeroSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℂ :=
  ∑' ρ : ℂ, chapter06ZeroSummand Z F ρ

noncomputable def chapter06ZeroPartialSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ ρ ∈ chapter06ZeroWindowFinset Z T, chapter06ZeroSummand Z F ρ

def chapter06ZeroContribution
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℝ :=
  (chapter06SymmetricZeroSum Z F).re

def chapter06ExplicitFormulaRightHandSide
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) : ℝ :=
  (chapter06Degree K : ℝ) * chapter06GammaConstant +
    (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
    4 * chapter06A F - (chapter06Degree K : ℝ) * chapter06B F -
    (chapter06RealPlaces K : ℝ) * chapter06C F +
    chapter06ZeroContribution Z F + chapter06PrimeContribution K F

/-! ### The contour and Laplace-inversion conventions -/

def chapter06ContourRectangle (c T : ℝ) : Set ℂ :=
  {s | 1 - c ≤ s.re ∧ s.re ≤ c ∧ |s.im| ≤ T}

def chapter06ContourIntegrand
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  chapter06LogDerivative (chapter06Xi K) s * chapter06Phi F s

noncomputable def chapter06RightVerticalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint c t) * Complex.I

noncomputable def chapter06LeftVerticalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    chapter06ContourIntegrand (K := K) F
      (chapter06VerticalLinePoint (1 - c) t) * Complex.I

noncomputable def chapter06TopHorizontalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ σ in c..(1 - c),
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint σ T)

noncomputable def chapter06BottomHorizontalIntegral
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  ∫ σ in (1 - c)..c,
    chapter06ContourIntegrand (K := K) F (chapter06VerticalLinePoint σ (-T))

noncomputable def chapter06HorizontalError
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (chapter06TopHorizontalIntegral (K := K) F c T +
      chapter06BottomHorizontalIntegral (K := K) F c T)

noncomputable def chapter06ContourResidueSum
    {K : Type*} [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ ρ ∈ chapter06ZeroWindowFinset Z T, chapter06ZeroSummand Z F ρ

noncomputable def chapter06LaplaceInversePartial
    (F : ℝ → ℝ) (c y T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
          Complex.exp (-((y : ℂ) *
            (chapter06VerticalLinePoint c t - (1 / 2 : ℂ)))) * Complex.I)

/-! ### Logarithmic derivatives and prime-power inversion -/

def chapter06ZetaLogDerivativeTerm
    {K : Type*} [Field K] [NumberField K]
    (q : Chapter06PrimePower K) (s : ℂ) : ℂ :=
  (Real.log (chapter06PrimeIdealNorm q.1 : ℝ) : ℂ) *
    (chapter06PrimeIdealNorm q.1 : ℂ) ^ (-((q.2.1 : ℂ) * s))

def chapter06ZetaLogDerivativeSeries
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∑' q : Chapter06PrimePower K, chapter06ZetaLogDerivativeTerm q s

def chapter06ZetaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  -chapter06LogDerivative
    (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K) s

def chapter06PoleLogDerivative (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

def chapter06DiscriminantLogDerivative
    (K : Type*) [Field K] [NumberField K] : ℂ :=
  (Real.log (chapter06AbsoluteDiscriminant K) : ℂ) / 2

def chapter06RealGammaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter06RealPlaces K : ℂ) * chapter06LogDerivative chapter06GammaReal s

def chapter06ComplexGammaLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (chapter06ComplexPlaces K : ℂ) * chapter06LogDerivative chapter06GammaComplex s

def chapter06ApproximateIdentity (η : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Integrable (η n)) ∧
    (∀ n, HasCompactSupport (η n)) ∧
    (∀ n, ContDiff ℝ ∞ (η n)) ∧
    (∀ n x, 0 ≤ η n x) ∧
    (∀ n x, η n (-x) = η n x) ∧
    (∀ n, ∫ x : ℝ, η n x = 1) ∧
    (∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)))

noncomputable def chapter06SmoothedConvolution
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05Convolution
    (η n) F

noncomputable def chapter06OriginCorrectionFactor
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  if chapter06SmoothedConvolution η F n 0 = 0 then 1 else
    (chapter06SmoothedConvolution η F n 0)⁻¹

noncomputable def chapter06SmoothedTestFunction
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => chapter06OriginCorrectionFactor η F n *
    chapter06SmoothedConvolution η F n x

/-! ### The source's limiting diagnostic -/

def chapter06AsymptoticExpression (α B C pole : ℝ) : ℝ :=
  chapter06GammaConstant + α * (Real.pi / 2) - pole - B - α * C

def chapter06UniversalLowerBoundExpression
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℝ :=
  (chapter06Degree K : ℝ) * chapter06GammaConstant +
    (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
    4 * chapter06A F - (chapter06Degree K : ℝ) * chapter06B F -
    (chapter06RealPlaces K : ℝ) * chapter06C F

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
