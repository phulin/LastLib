import Mathlib.Analysis.Fourier.Convolution
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory

/-! ## 5.3. Positive type and autocorrelation -/

theorem chapter05_autocorrelation_fourier_eq_normSq
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (hL2 : MemLp h 2 volume) (t : ℝ) :
    chapter05FourierTransform (chapter05Autocorrelation h) t =
      (Complex.normSq (chapter05FourierTransform h t) : ℂ) := by
  sorry

/-- The value at the origin is the squared `L²` mass of the input. -/
theorem chapter05_autocorrelation_apply_zero_eq_l2_sq
    (h : ℝ → ℝ) (hL2 : MemLp h 2 volume) :
    chapter05Autocorrelation h 0 = ∫ x : ℝ, h x ^ 2 ∂volume := by
  sorry

/-- Strict positivity requires nonvanishing modulo almost-everywhere equality. -/
theorem chapter05_autocorrelation_apply_zero_pos
    (h : ℝ → ℝ) (hL2 : MemLp h 2 volume)
    (hNeZero : ¬ h =ᵐ[volume] (0 : ℝ → ℝ)) :
    0 < chapter05Autocorrelation h 0 := by
  sorry

theorem chapter05_autocorrelation_is_even
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (hL2 : MemLp h 2 volume) :
    Function.Even (chapter05Autocorrelation h) := by
  sorry

theorem chapter05_autocorrelation_is_positive_type
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (hL2 : MemLp h 2 volume) :
    Chapter05PositiveType (chapter05Autocorrelation h) := by
  sorry

theorem chapter05_positive_type_real_transform_nonnegative
    {G : ℝ → ℝ} (hG : Chapter05PositiveType G) :
    ∀ t : ℝ, 0 ≤ chapter05RealFourierTransform G t := by
  sorry

@[simp] theorem chapter05_normalizeAtZero_apply_zero
    (G : ℝ → ℝ) (hG0 : G 0 ≠ 0) :
    chapter05NormalizeAtZero G hG0 0 = 1 := by
  sorry

theorem chapter05_positive_type_does_not_imply_pointwise_nonnegative :
    ∃ G : ℝ → ℝ, Chapter05PositiveType G ∧ ∃ x : ℝ, G x < 0 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
