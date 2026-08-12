import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory

/-! ## 5.4. The two positivity regimes -/

theorem chapter05_unconditionally_admissible_iff
    {F : ℝ → ℝ} :
    Chapter05UnconditionallyAdmissible F ↔
      Chapter05BasicallyAdmissible F ∧
        ∃ witness : ℝ → ℝ,
          (∀ x : ℝ, 0 ≤ witness x) ∧
            Function.Even witness ∧
                Chapter05PositiveType witness ∧
                  (∀ x : ℝ, F x = witness x / Real.cosh (x / 2)) := Iff.rfl

theorem chapter05_grh_admissible_iff
    {F : ℝ → ℝ} :
    Chapter05GRHAdmissible F ↔
      Chapter05BasicallyAdmissible F ∧
        (∀ x : ℝ, 0 ≤ F x) ∧
          (∀ t : ℝ,
            (chapter05FourierTransform F t).im = 0 ∧
              0 ≤ (chapter05FourierTransform F t).re) := by
  constructor
  · intro hF
    exact ⟨hF.basic, hF.pointwiseNonnegative, hF.transformNonnegative⟩
  · intro hF
    exact
      { basic := hF.1
        pointwiseNonnegative := hF.2.1
        transformNonnegative := hF.2.2 }

theorem chapter05_grh_admissible_real_transform_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) :
    ∀ t : ℝ, 0 ≤ chapter05RealFourierTransform F t := by
  sorry

theorem chapter05_grh_admissible_central_line_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) (t : ℝ) :
    (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
      0 ≤ (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  sorry

theorem chapter05_grh_admissible_lower_bound_admissible
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) :
    Chapter05LowerBoundAdmissible F := by
  exact ⟨hF.basic, hF.pointwiseNonnegative⟩

/-
DEPENDENCY_GUESS: The later explicit-formula chapter should consume the
central-line statement above together with a `GRH` zero-location predicate;
this chapter intentionally records the transform positivity interface rather
than guessing the number-field zeta API before that chapter is reconciled.
-/

theorem chapter05_unconditionally_admissible_pointwise_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    ∀ x : ℝ, 0 ≤ F x := by
  sorry

theorem chapter05_unconditionally_admissible_lower_bound_admissible
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    Chapter05LowerBoundAdmissible F := by
  exact ⟨hF.1, chapter05_unconditionally_admissible_pointwise_nonnegative hF⟩

theorem chapter05_unconditionally_admissible_strip_paired_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    chapter05StripPairedNonnegative F := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
