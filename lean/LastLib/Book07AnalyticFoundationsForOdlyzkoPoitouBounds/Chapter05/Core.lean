import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Support

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

/-!
Shared interfaces for Chapter 5, in the source order of §5.1--§5.4.

The earlier Book07 chapters are drafted independently, so this file keeps the
book-facing transform and test-function interfaces independent of any future
explicit-formula implementation.  The integrals use the pinned Mathlib
Lebesgue/Bochner conventions; the Fourier transform below retains the book's
angular-frequency normalization (no factor of `2 * π`).
-/

/-! ## 5.1. Transform conventions -/

/-- The complex Fourier transform with the book's angular-frequency convention. -/
def chapter05FourierTransform (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ) * Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume

/-- The real-valued cosine form of the Fourier transform used for order statements. -/
def chapter05RealFourierTransform (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, F x * Real.cos (t * x) ∂volume

/-- The bilateral Laplace transform centered at `1 / 2`. -/
def chapter05LaplaceKernel (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))

def chapter05BilateralLaplaceTransform (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ) * chapter05LaplaceKernel s x ∂volume

/-! ## 5.2. The basic admissible class -/

/-- A finite-exception-set formulation of piecewise `C^2`. -/
def chapter05PiecewiseC2 (F : ℝ → ℝ) : Prop :=
  ∃ s : Set ℝ, s.Finite ∧ ∀ x ∉ s, ContDiffAt ℝ 2 F x

/-- One-sided first derivatives, with the left/right conventions made explicit. -/
def Chapter05OneSidedDerivativeBV (F : ℝ → ℝ) : Prop :=
  ∃ leftDerivative rightDerivative : ℝ → ℝ,
    (∀ x, HasDerivWithinAt F (leftDerivative x) (Iic x) x) ∧
      (∀ x, HasDerivWithinAt F (rightDerivative x) (Ici x) x) ∧
      BoundedVariationOn leftDerivative univ ∧
        BoundedVariationOn rightDerivative univ

/-- The nonnegative integral appearing in (5.1), represented by its
`ENNReal`-valued Lebesgue integral so that finiteness is meaningful. -/
def chapter05OriginIntegral (F : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (|1 - F x| / x)

def chapter05OriginCondition (F : ℝ → ℝ) : Prop :=
  chapter05OriginIntegral F < ⊤

/-- The class called basically admissible in §5.2. -/
structure Chapter05BasicallyAdmissible (F : ℝ → ℝ) : Prop where
  even : Function.Even F
  continuous : Continuous F
  compactSupport : HasCompactSupport F
  piecewiseC2 : chapter05PiecewiseC2 F
  valueAtZero : F 0 = 1
  oneSidedDerivativeBV : Chapter05OneSidedDerivativeBV F
  originCondition : chapter05OriginCondition F

/-! Basic admissibility makes the transform integrals available without
repeating the compact-support argument at every use site. -/

theorem chapter05_basically_admissible_integrable
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Integrable F volume := by
  exact hF.continuous.integrable_of_hasCompactSupport hF.compactSupport

theorem chapter05_basically_admissible_laplace_integrable
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) (s : ℂ) :
    Integrable
      (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x) volume := by
  exact (by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp hF.continuous).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    · exact (hF.compactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right)

/-! The common extra hypothesis used when a lower-bound argument discards the
prime-side contribution. -/

def Chapter05LowerBoundAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter05BasicallyAdmissible F ∧ ∀ x : ℝ, 0 ≤ F x

/-! ## 5.3. Positive type and autocorrelation -/

/-- Reflection of a real function in the convolution variable. -/
def chapter05Reflect (h : ℝ → ℝ) : ℝ → ℝ :=
  fun x => h (-x)

/-- Real convolution with respect to Lebesgue measure, using Mathlib's canonical
continuous bilinear convolution operator. -/
noncomputable def chapter05Convolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The autocorrelation `h * \tilde h`. -/
noncomputable def chapter05Autocorrelation (h : ℝ → ℝ) : ℝ → ℝ :=
  chapter05Convolution h (chapter05Reflect h)

/-- A continuous integrable real function whose complex Fourier transform is
real and everywhere nonnegative.  This records the order assertion in the
source without silently discarding a possible odd/imaginary component. -/
structure Chapter05PositiveType (G : ℝ → ℝ) : Prop where
  continuous : Continuous G
  integrable : Integrable G volume
  transformNonnegative : ∀ t : ℝ,
    (chapter05FourierTransform G t).im = 0 ∧
      0 ≤ (chapter05FourierTransform G t).re

/-- Normalize a function at a specified nonzero value at the origin. -/
def chapter05NormalizeAtZero (G : ℝ → ℝ) (_hG0 : G 0 ≠ 0) : ℝ → ℝ :=
  fun x => G x / G 0

/-! ## 5.4. The two positivity regimes -/

/-- GRH-admissibility: basic admissibility plus pointwise and Fourier positivity. -/
structure Chapter05GRHAdmissible (F : ℝ → ℝ) : Prop where
  basic : Chapter05BasicallyAdmissible F
  pointwiseNonnegative : ∀ x : ℝ, 0 ≤ F x
  transformNonnegative : ∀ t : ℝ,
    (chapter05FourierTransform F t).im = 0 ∧
      0 ≤ (chapter05FourierTransform F t).re

/-- Unconditional admissibility: the strip-positive shape `G / cosh(x / 2)`. -/
def Chapter05UnconditionallyAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter05BasicallyAdmissible F ∧
    ∃ witness : ℝ → ℝ,
      (∀ x : ℝ, 0 ≤ witness x) ∧
        Function.Even witness ∧
          Chapter05PositiveType witness ∧
            (∀ x : ℝ, F x = witness x / Real.cosh (x / 2))

/-- The paired transform corresponding to the functional-equation pairing
`β + i γ ↔ 1 - β + i γ`. -/
def chapter05PairedLaplaceTransform (F : ℝ → ℝ) (β γ : ℝ) : ℂ :=
  chapter05BilateralLaplaceTransform F ((β : ℂ) + (γ : ℂ) * Complex.I) +
    chapter05BilateralLaplaceTransform F (((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I)

/-- The real nonnegativity assertion needed for the unconditional zero pairing. -/
def chapter05StripPairedNonnegative (F : ℝ → ℝ) : Prop :=
  ∀ β γ : ℝ, 0 ≤ β → β ≤ 1 →
    (chapter05PairedLaplaceTransform F β γ).im = 0 ∧
      0 ≤ (chapter05PairedLaplaceTransform F β γ).re

/-! ## Shared decay interface used by the zero-sum bridge -/

/-- Uniform `O_F((1 + |t|)⁻²)` decay on every fixed bounded vertical strip. -/
def chapter05VerticalTransformDecay2 (F : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
    ∀ σ t : ℝ, |σ| ≤ R →
      ‖chapter05BilateralLaplaceTransform F
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
