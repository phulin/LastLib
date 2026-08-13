import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-! ## 5.1. Transform conventions -/

/-- The angular-frequency convention is Mathlib's Fourier transform evaluated at
`t / (2 * π)`, since pinned Mathlib uses the `2 * π` frequency convention. -/
theorem chapter05_fourierTransform_eq_mathlib_angular
    (F : ℝ → ℝ) (hF : Integrable F volume) (t : ℝ) :
    chapter05FourierTransform F t =
      𝓕 (fun x : ℝ => (F x : ℂ)) (t / (2 * Real.pi)) := by
  sorry

theorem chapter05_laplace_reflection
    {F : ℝ → ℝ} (hEven : Function.Even F)
    (hInt : ∀ s : ℂ,
      Integrable (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x) volume)
    (s : ℂ) :
    chapter05BilateralLaplaceTransform F s =
      chapter05BilateralLaplaceTransform F (1 - s) := by
  sorry

theorem chapter05_laplace_entire_of_continuous_compactSupport
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hCompactSupport : HasCompactSupport F) :
    Differentiable ℂ (chapter05BilateralLaplaceTransform F) := by
  sorry

theorem chapter05_laplace_on_critical_line_eq_fourier_neg
    {F : ℝ → ℝ} {t : ℝ}
    (hInt : Integrable
      (fun x : ℝ => (F x : ℂ) *
        chapter05LaplaceKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) x) volume) :
    chapter05BilateralLaplaceTransform F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      chapter05FourierTransform F (-t) := by
  sorry

theorem chapter05_fourier_transform_neg_eq
    {F : ℝ → ℝ} (hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05FourierTransform F (-t) = chapter05FourierTransform F t := by
  sorry

theorem chapter05_laplace_on_critical_line
    {F : ℝ → ℝ} (hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05BilateralLaplaceTransform F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      chapter05FourierTransform F t := by
  sorry

theorem chapter05_fourier_transform_eq_ofReal_real_transform
    {F : ℝ → ℝ} (hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05FourierTransform F t =
      (chapter05RealFourierTransform F t : ℂ) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
