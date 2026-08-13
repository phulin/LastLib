import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Topology.Algebra.Support
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-!
Shared interfaces for Chapter 8.  The preceding Book 7 chapters are developed as separate
modules in this workspace, so the two small interfaces below record exactly the earlier
hypotheses used here: the basic test-function conditions and the equality supplied by the explicit
formula.  They are interfaces, rather than additional assumptions built into any conclusions.
-/

abbrev Chapter08Degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

abbrev Chapter08RealPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

abbrev Chapter08ComplexPlaceCount (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

def Chapter08AbsoluteDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(NumberField.discr K : ℝ)|

abbrev Chapter08RootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.rootDiscr K

def chapter08SignatureProportion (K : Type*) [Field K] [NumberField K] : ℝ :=
  (Chapter08RealPlaceCount K : ℝ) / (Chapter08Degree K : ℝ)

def Chapter08Even (F : ℝ → ℝ) : Prop :=
  ∀ x, F (-x) = F x

def Chapter08PiecewiseC2 (F : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∀ x ∉ (s : Set ℝ),
    ∃ ε : ℝ, 0 < ε ∧ ContDiffOn ℝ 2 F (Set.Ioo (x - ε) (x + ε))

def Chapter08FirstDerivativeBoundedVariation (F : ℝ → ℝ) : Prop :=
  ∃ Dleft Dright : ℝ → ℝ,
    (∀ a b : ℝ, BoundedVariationOn Dleft (Set.uIcc a b)) ∧
      (∀ a b : ℝ, BoundedVariationOn Dright (Set.uIcc a b)) ∧
      (∀ x : ℝ,
        HasDerivWithinAt F (Dright x) (Set.Ici x) x ∧
          HasDerivWithinAt F (Dleft x) (Set.Iic x) x)

def Chapter08BasicallyAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08Even F ∧
    Continuous F ∧
    HasCompactSupport F ∧
    Chapter08PiecewiseC2 F ∧
    Chapter08FirstDerivativeBoundedVariation F ∧
    F 0 = 1 ∧
    IntegrableOn (fun x : ℝ => |1 - F x| / x) (Set.Ioc 0 1)

def Chapter08PointwiseNonnegative (F : ℝ → ℝ) : Prop :=
  ∀ x, 0 ≤ F x

/- The cosine form is the real-valued restriction of the angular-frequency transform for even
functions.  Chapter 5 already provides the book-facing positive-type interface, whose complex
transform formulation does not add evenness as an extra hypothesis. -/
def chapter08CosineTransform (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, F x * Real.cos (t * x)

def chapter08FourierTransform (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

theorem chapter08_fourier_transform_eq_chapter05
    (F : ℝ → ℝ) (t : ℝ) :
    chapter08FourierTransform F t = Chapter05.chapter05FourierTransform F t := by
  unfold chapter08FourierTransform Chapter05.chapter05FourierTransform
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  push_cast
  ring_nf

abbrev Chapter08PositiveType (F : ℝ → ℝ) : Prop :=
  Chapter05.Chapter05PositiveType F

def Chapter08GRHAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08BasicallyAdmissible F ∧
    Chapter08PointwiseNonnegative F ∧
    Chapter08PositiveType F

def Chapter08UnconditionallyAdmissible (F : ℝ → ℝ) : Prop :=
  Chapter08BasicallyAdmissible F ∧
    ∃ G : ℝ → ℝ,
      Chapter08Even G ∧
        Chapter08PointwiseNonnegative G ∧
        Chapter08PositiveType G ∧
        ∀ x, F x = G x / Real.cosh (x / 2)

def chapter08A (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, F x * Real.cosh (x / 2)

def chapter08B (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))

def chapter08C (F : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))

/-!
This is the local dependency guess for Theorem 6.1.  The fields are the zero and prime
contributions from that theorem; no positivity is built into the structure, since positivity is
the separate input used by the Chapter 8 lower-bound theorem.
-/
structure Chapter08ExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) where
  basicAdmissible : Chapter08BasicallyAdmissible F
  zeroContribution : ℝ
  primeContribution : ℝ
  identity :
    Real.log (Chapter08AbsoluteDiscriminant K) =
      (Chapter08Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (Chapter08RealPlaceCount K : ℝ) * (Real.pi / 2) -
        4 * chapter08A F -
        (Chapter08Degree K : ℝ) * chapter08B F -
        (Chapter08RealPlaceCount K : ℝ) * chapter08C F +
        zeroContribution + primeContribution

theorem chapter08_fourier_transform_eq_cosine_of_even
    {F : ℝ → ℝ} (hF : Integrable F) (heven : Chapter08Even F) (t : ℝ) :
    chapter08FourierTransform F t = (chapter08CosineTransform F t : ℂ) := by
  let q : ℝ → ℝ := fun x =>
    ((F x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))).im
  have hfc : Integrable (fun x : ℝ =>
      (F x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
    apply hF.mono (by fun_prop)
    filter_upwards with x
    simp [Complex.norm_exp]
  have hq : ∀ x, q (-x) = -q x := by
    intro x
    change ((F (-x) : ℂ) * Complex.exp
      (-Complex.I * (t : ℂ) * ((-x : ℝ) : ℂ))).im =
      -((F x : ℂ) * Complex.exp
        (-Complex.I * (t : ℂ) * (x : ℂ))).im
    rw [heven]
    simp [Complex.mul_im, Complex.exp_re, Complex.exp_im, Real.sin_neg]
  have hqeq : (∫ x : ℝ, q x) = -∫ x : ℝ, q x := by
    have hqint : (∫ x : ℝ, q (-x)) = ∫ x : ℝ, q x :=
      MeasureTheory.integral_neg_eq_self q volume
    calc
      (∫ x : ℝ, q x) = ∫ x : ℝ, q (-x) := hqint.symm
      _ = ∫ x : ℝ, -q x :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => hq x))
      _ = -∫ x : ℝ, q x := integral_neg q
  have hqzero : (∫ x : ℝ, q x) = 0 := by
    linarith [hqeq]
  unfold chapter08FourierTransform chapter08CosineTransform
  apply Complex.ext
  · have hreal : ∀ x : ℝ,
        ((F x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))).re =
          F x * Real.cos (t * x) := by
      intro x
      simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, Real.cos_neg]
    calc
      (∫ x : ℝ, (F x : ℂ) * Complex.exp
          (-Complex.I * (t : ℂ) * (x : ℂ))).re =
          ∫ x : ℝ, ((F x : ℂ) * Complex.exp
          (-Complex.I * (t : ℂ) * (x : ℂ))).re := (integral_re hfc).symm
      _ = ∫ x : ℝ, F x * Real.cos (t * x) :=
        integral_congr_ae (Filter.Eventually.of_forall hreal)
      _ = (↑(∫ x : ℝ, F x * Real.cos (t * x)) : ℂ).re := by simp
  · calc
      (∫ x : ℝ, (F x : ℂ) * Complex.exp
          (-Complex.I * (t : ℂ) * (x : ℂ))).im =
          ∫ x : ℝ, ((F x : ℂ) * Complex.exp
            (-Complex.I * (t : ℂ) * (x : ℂ))).im := (integral_im hfc).symm
      _ = ∫ x : ℝ, q x := rfl
      _ = 0 := hqzero
      _ = (↑(∫ x : ℝ, F x * Real.cos (t * x)) : ℂ).im := by simp

theorem chapter08_positive_type_iff_angular_transform_nonnegative
    {F : ℝ → ℝ} (heven : Chapter08Even F) :
    Chapter08PositiveType F ↔
      Continuous F ∧ Integrable F ∧
        ∀ t, 0 ≤ (chapter08FourierTransform F t).re ∧
          (chapter08FourierTransform F t).im = 0 := by
  constructor
  · intro hF
    refine ⟨hF.continuous, hF.integrable, ?_⟩
    intro t
    have hfourier :=
      chapter08_fourier_transform_eq_cosine_of_even hF.integrable heven t
    have hre : (chapter08FourierTransform F t).re = chapter08CosineTransform F t := by
      rw [hfourier]
      simp
    have htransform := hF.transformNonnegative t
    rw [← chapter08_fourier_transform_eq_chapter05 F t] at htransform
    refine ⟨?_, ?_⟩
    · exact htransform.2
    · exact htransform.1
  · rintro ⟨hcont, hint, hnonneg⟩
    refine ⟨hcont, hint, ?_⟩
    intro t
    have hfourier :=
      chapter08_fourier_transform_eq_cosine_of_even hint heven t
    have hre : (chapter08FourierTransform F t).re = chapter08CosineTransform F t := by
      rw [hfourier]
      simp
    have htransform :
        0 ≤ (chapter08FourierTransform F t).re ∧
          (chapter08FourierTransform F t).im = 0 := by
      exact ⟨(hnonneg t).1, (hnonneg t).2⟩
    refine ⟨?_, ?_⟩
    · rw [← chapter08_fourier_transform_eq_chapter05 F t]
      exact htransform.2
    · rw [← chapter08_fourier_transform_eq_chapter05 F t]
      exact htransform.1

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
