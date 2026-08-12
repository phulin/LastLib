import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory

/-! ## 5.3. Positive type and autocorrelation -/

/-
SOURCE_ISSUE: The source says “If `h ∈ L²(ℝ)` is real ...
`G = h * \tilde h`, `\widehat G = |\widehat h|² ≥ 0`.”  An `L²` function
need not be integrable, so the stated pointwise Fourier transform and the
integrability required in the preceding definition are not available from
that hypothesis alone.  The minimal correction used below is `h ∈ L¹ ∩ L²`.
-/
theorem chapter05_autocorrelation_fourier_eq_normSq
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (hL2 : MemLp h 2 volume) (t : ℝ) :
    chapter05FourierTransform (chapter05Autocorrelation h) t =
      (Complex.normSq (chapter05FourierTransform h t) : ℂ) := by
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

/-
SOURCE_ISSUE: The sentence “After division by `G(0)`, one has `G(0)=1`”
requires `G(0) ≠ 0` (in the positive-type setting one normally assumes a
nonzero positive-type function, which gives the stronger `G(0) > 0`).  The
normalization definition therefore takes nonvanishing explicitly.
-/
@[simp] theorem chapter05_normalizeAtZero_apply_zero
    (G : ℝ → ℝ) (hG0 : G 0 ≠ 0) :
    chapter05NormalizeAtZero G hG0 0 = 1 := by
  sorry

/-
SOURCE_ISSUE: In the source phrase “A continuous integrable function `G` is
of positive type when `\widehat G(t) ≥ 0`,” the codomain/parity needed to
interpret an order on Fourier values is implicit.  `Chapter05PositiveType`
uses real-valued `G` and records that its complex Fourier transform is real
and nonnegative.
-/
theorem chapter05_positive_type_does_not_imply_pointwise_nonnegative :
    ∃ G : ℝ → ℝ, Chapter05PositiveType G ∧ ∃ x : ℝ, G x < 0 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
