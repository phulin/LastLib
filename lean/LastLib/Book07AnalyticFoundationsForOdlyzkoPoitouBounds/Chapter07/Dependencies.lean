import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

/-!
Shared interfaces for Chapter 7.

Chapter 5 supplies the book's transform conventions.  The chapter-specific
zero-spectrum, positive-type, and tempered-measure interfaces below remain
local because Chapter 6's zero package is parameterized by a number field and
uses a different symmetry presentation.  The normalizations are recorded
explicitly: the book Fourier transform is `∫ f x exp (-I * t * x) dx`.
-/

abbrev Chapter07TestFunction := ℝ → ℝ

abbrev chapter07Even (f : Chapter07TestFunction) : Prop :=
  Function.Even f

def chapter07PointwiseNonnegative (f : Chapter07TestFunction) : Prop :=
  ∀ x, 0 ≤ f x

abbrev chapter07FourierTransform
    (f : Chapter07TestFunction) (t : ℝ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform f t

/- The same kernel with a complex frequency, expressed through Chapter 5's
   centered bilateral transform for the holomorphic strip calculation. -/
abbrev chapter07ComplexFourierTransform
    (f : Chapter07TestFunction) (z : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform
    f ((1 / 2 : ℂ) - Complex.I * z)

theorem chapter07FourierTransform_eq_integral
    (f : Chapter07TestFunction) (t : ℝ) :
    chapter07FourierTransform f t =
      ∫ x : ℝ, (f x : ℂ) * Complex.exp
        (-Complex.I * (t : ℂ) * (x : ℂ)) := by
  simp [chapter07FourierTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform,
    mul_assoc]

theorem chapter07ComplexFourierTransform_ofReal
    (f : Chapter07TestFunction) (t : ℝ) :
    chapter07ComplexFourierTransform f (t : ℂ) =
      chapter07FourierTransform f t := by
  simp [chapter07ComplexFourierTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel,
    chapter07FourierTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform,
    mul_assoc]

abbrev chapter07CosineTransform
    (f : Chapter07TestFunction) (t : ℝ) : ℝ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05RealFourierTransform f t

theorem chapter07FourierTransform_re_eq_cosineTransform
    (f : Chapter07TestFunction) (hf : Integrable f) (t : ℝ) :
    (chapter07FourierTransform f t).re = chapter07CosineTransform f t := by
  have hreal : Integrable (fun x : ℝ => (f x : ℂ)) := hf.ofReal
  have hcomplex_integrable : Integrable (fun x : ℝ =>
      (f x : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
    apply (hreal.congr' ?_ ?_)
    · exact hf.ofReal.aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by fun_prop))
    · filter_upwards [] with x
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_exp]
      simp
  rw [chapter07FourierTransform_eq_integral]
  change (∫ x : ℝ, (f x : ℂ) * Complex.exp
      (-Complex.I * (t : ℂ) * (x : ℂ))).re =
    ∫ x : ℝ, f x * Real.cos (t * x)
  calc
    (∫ x : ℝ, (f x : ℂ) * Complex.exp
      (-Complex.I * (t : ℂ) * (x : ℂ))).re =
        ∫ x : ℝ, ((f x : ℂ) * Complex.exp
          (-Complex.I * (t : ℂ) * (x : ℂ))).re :=
      (integral_re hcomplex_integrable).symm
    _ = ∫ x : ℝ, f x * Real.cos (t * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.mul_re, Complex.exp_re]
      simp

theorem chapter07FourierTransform_im_eq_zero_of_even
    (f : Chapter07TestFunction) (hf : Integrable f) (heven : chapter07Even f) (t : ℝ) :
    (chapter07FourierTransform f t).im = 0 := by
  have h :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_fourier_transform_eq_ofReal_real_transform
      hf heven t
  have h' : chapter07FourierTransform f t =
      (chapter07CosineTransform f t : ℂ) := h
  rw [h']
  rfl

/- Positive definiteness is the continuous finite positive-semidefinite-kernel
   condition.  It is kept separate from the book's integrable Fourier-positive
   notion because endpoint kernels and examples such as the cosine wave need
   not be integrable. -/
def chapter07PositiveDefinite (f : Chapter07TestFunction) : Prop :=
  Continuous f ∧
    ∀ n : ℕ, ∀ x : Fin n → ℝ, ∀ c : Fin n → ℂ,
      0 ≤ (∑ i, ∑ j, c i * star (c j) * (f (x i - x j) : ℂ)).re ∧
        (∑ i, ∑ j, c i * star (c j) * (f (x i - x j) : ℂ)).im = 0

/- The book's positive-type condition from §5.3, reused here rather than
   replacing it by the stronger-looking finite-kernel presentation. -/
abbrev chapter07PositiveType (f : Chapter07TestFunction) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05PositiveType f

def chapter07FourierNonnegative (f : Chapter07TestFunction) : Prop :=
  Integrable f ∧
    ∀ t : ℝ,
      0 ≤ (chapter07FourierTransform f t).re ∧
        (chapter07FourierTransform f t).im = 0

theorem chapter07_positiveType_mul
    (f g : Chapter07TestFunction)
    (hf : chapter07PositiveType f) (hg : chapter07PositiveType g) :
    chapter07PositiveType (fun x => f x * g x) := by
  sorry

theorem chapter07_positiveType_fourierNonnegative
    (f : Chapter07TestFunction) (hpositive : chapter07PositiveType f) :
    chapter07FourierNonnegative f := by
  refine ⟨hpositive.integrable, ?_⟩
  intro t
  exact ⟨(hpositive.transformNonnegative t).2,
    (hpositive.transformNonnegative t).1⟩

/- The convolution convention matching the book Fourier normalization. -/
noncomputable def chapter07ComplexConvolution
    (u v : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ, u s * v (t - s)

theorem chapter07_fourierTransform_mul_eq_inv_two_pi_convolution
    (f g : Chapter07TestFunction)
    (hf : Integrable f) (hg : Integrable g)
    (hfhat : Integrable (chapter07FourierTransform f))
    (hghat : Integrable (chapter07FourierTransform g)) (t : ℝ) :
    chapter07FourierTransform (fun x => f x * g x) t =
      (1 / (2 * (Real.pi : ℂ))) *
        chapter07ComplexConvolution (chapter07FourierTransform f)
          (chapter07FourierTransform g) t := by
  sorry

def chapter07ZeroPartner (ρ : ℂ) : ℂ :=
  1 - star ρ

theorem chapter07ZeroPartner_involutive (ρ : ℂ) :
    chapter07ZeroPartner (chapter07ZeroPartner ρ) = ρ := by
  simp [chapter07ZeroPartner]

structure Chapter07ZeroSpectrum where
  support : Set ℂ
  multiplicity : ℂ → ℕ
  support_iff_multiplicity_ne_zero :
    ∀ ρ, ρ ∈ support ↔ multiplicity ρ ≠ 0
  critical_strip :
    ∀ {ρ}, ρ ∈ support → 0 ≤ ρ.re ∧ ρ.re ≤ 1
  functional_equation_partner :
    ∀ {ρ}, ρ ∈ support ↔ chapter07ZeroPartner ρ ∈ support
  conjugation_partner :
    ∀ {ρ}, ρ ∈ support ↔ star ρ ∈ support
  multiplicity_partner :
    ∀ ρ, multiplicity (chapter07ZeroPartner ρ) = multiplicity ρ
  multiplicity_conjugation_partner :
    ∀ ρ, multiplicity (star ρ) = multiplicity ρ
  locally_finite :
    ∀ R : ℝ, Set.Finite {ρ : ℂ | ρ ∈ support ∧ ‖ρ‖ ≤ R}

/- The canonical zero package is parameterized by the number field in Chapter
   6.  This view retains its support, both partner symmetries, multiplicities,
   and local-finiteness data while presenting the functional-equation partner
   used by the strip argument. -/
abbrev Chapter07CanonicalZeroSpectrum
    (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Chapter06ZeroSpectrum K

def chapter07ZeroSpectrumOfChapter06
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) : Chapter07ZeroSpectrum where
  support := Z.support
  multiplicity := Z.multiplicity
  support_iff_multiplicity_ne_zero := Z.support_iff_multiplicity_ne_zero
  critical_strip := Z.critical_strip
  functional_equation_partner := by
    intro ρ
    constructor
    · intro hρ
      have hρ' : star ρ ∈ Z.support :=
        (Z.conjugation_partner (ρ := ρ)).1 hρ
      simpa [chapter07ZeroPartner] using
        (Z.functional_equation_partner (ρ := star ρ)).1 hρ'
    · intro hρ
      have hρ' : 1 - star ρ ∈ Z.support := by
        simpa [chapter07ZeroPartner] using hρ
      have hρ'' : star ρ ∈ Z.support :=
        (Z.functional_equation_partner (ρ := star ρ)).2 hρ'
      exact (Z.conjugation_partner (ρ := ρ)).2 hρ''
  conjugation_partner := Z.conjugation_partner
  multiplicity_partner := by
    intro ρ
    simpa [chapter07ZeroPartner] using
      (Z.multiplicity_functional_equation_partner (star ρ)).trans
        (Z.multiplicity_conjugation_partner ρ)
  multiplicity_conjugation_partner := Z.multiplicity_conjugation_partner
  locally_finite := by
    intro R
    refine (Z.locally_finite (R + 1)).subset ?_
    intro ρ hρ
    refine ⟨hρ.1, ?_⟩
    have him_sq : ρ.im * ρ.im ≤ ‖ρ‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using Complex.im_sq_le_normSq ρ
    have him : |ρ.im| ≤ ‖ρ‖ := by
      exact abs_le_of_sq_le_sq (by simpa [pow_two] using him_sq) (norm_nonneg ρ)
    exact lt_of_le_of_lt (him.trans hρ.2) (by linarith)

def chapter07GRH (Z : Chapter07ZeroSpectrum) : Prop :=
  ∀ ρ, ρ ∈ Z.support →
    ∃ γ : ℝ, ρ = (1 / 2 : ℂ) + Complex.I * (γ : ℂ)

def chapter07CanonicalGRH
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) : Prop :=
  chapter07GRH (chapter07ZeroSpectrumOfChapter06 K Z)

abbrev chapter07ZeroTransform
    (f : Chapter07TestFunction) (ρ : ℂ) : ℂ :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform f ρ

theorem chapter07ZeroTransform_eq_complexFourierTransform
    (f : Chapter07TestFunction) (ρ : ℂ) :
    chapter07ZeroTransform f ρ =
      chapter07ComplexFourierTransform f
        (Complex.I * (ρ - (1 / 2 : ℂ))) := by
  simp only [chapter07ZeroTransform, chapter07ComplexFourierTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  rw [← mul_assoc, Complex.I_mul_I]
  simp

def chapter07ZeroTermSummand
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction) (ρ : ℂ) : ℂ :=
  (Z.multiplicity ρ : ℂ) * chapter07ZeroTransform f ρ

theorem chapter07_zeroTermSummand_of_chapter06
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K)
    (f : Chapter07TestFunction) (ρ : ℂ) :
    chapter07ZeroTermSummand (chapter07ZeroSpectrumOfChapter06 K Z) f ρ =
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
        Z f ρ := by
  rfl

def chapter07ZeroTermConvergent
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction) : Prop :=
  Summable (chapter07ZeroTermSummand Z f)

noncomputable def chapter07ZeroTerm
    (Z : Chapter07ZeroSpectrum) (f : Chapter07TestFunction) : ℝ :=
  (∑' ρ : ℂ, chapter07ZeroTermSummand Z f ρ).re

/- A tempered Fourier representation is stated on Schwartz test functions;
   this is the endpoint formulation needed for the constant function. -/
noncomputable def chapter07FourierDistributionPairing
    (f : Chapter07TestFunction) (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ x : ℝ, (f x : ℂ) *
    (∫ t : ℝ, φ t * Complex.exp
      (-Complex.I * (t : ℂ) * (x : ℂ)))

def chapter07TemperedFourierRepresentation
    (f : Chapter07TestFunction) (μ : Measure ℝ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ,
    chapter07FourierDistributionPairing f φ = ∫ t : ℝ, φ t ∂μ

def chapter07MeasurePositiveOnSchwartz (μ : Measure ℝ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℝ, (∀ x, 0 ≤ φ x) →
    0 ≤ ∫ x : ℝ, φ x ∂μ

def chapter07MeasureTempered (μ : Measure ℝ) : Prop :=
  ∃ C : ℝ, ∃ m : ℕ, 0 ≤ C ∧
    ∀ R : ℝ, 1 ≤ R →
      μ (Metric.closedBall (0 : ℝ) R) ≤ ENNReal.ofReal (C * R ^ m)

def chapter07PositiveTemperedType (f : Chapter07TestFunction) : Prop :=
  ∃ μ : Measure ℝ,
    chapter07TemperedFourierRepresentation f μ ∧
      chapter07MeasureTempered μ ∧ IsLocallyFiniteMeasure μ ∧
        chapter07MeasurePositiveOnSchwartz μ

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
