import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! ### 6.2. The truncated contour identity -/

theorem chapter06_contour_rectangle_mem_iff
    {c T : ℝ} {z : ℂ} :
    z ∈ chapter06ContourRectangle c T ↔
      1 - c ≤ z.re ∧ z.re ≤ c ∧ |z.im| ≤ T := by
  rfl

theorem chapter06_phi_functional_equation_symmetry
    {F : ℝ → ℝ} (hF : Chapter06SmoothCompactSupport F) :
    ∀ s : ℂ, chapter06Phi F (1 - s) = chapter06Phi F s := by
  sorry

theorem chapter06_xi_functional_equation
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) :
    ∀ s : ℂ, chapter06Xi K s = chapter06Xi K (1 - s) := by
  exact P.functional_equation

theorem chapter06_xi_conjugation_symmetry
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) :
    ∀ s : ℂ, chapter06Xi K (star s) = star (chapter06Xi K s) := by
  exact P.conjugation_symmetry

theorem chapter06_xi_log_derivative_functional_equation
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {s : ℂ}
    (hs : chapter06Xi K s ≠ 0)
    (hsym : chapter06Xi K (1 - s) ≠ 0) :
    chapter06LogDerivative (chapter06Xi K) (1 - s) =
      -chapter06LogDerivative (chapter06Xi K) s := by
  sorry

theorem chapter06_log_derivative_zero_pole_residue
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {ρ : ℂ}
    (hρ : ρ ∈ P.zeros.support) :
    chapter06SimplePoleWithResidue
      (chapter06LogDerivative (chapter06Xi K)) ρ
      (P.zeros.multiplicity ρ : ℂ) := by
  exact P.zeros.log_derivative_simple_pole hρ

theorem chapter06_left_vertical_integral_substitution
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c T : ℝ}
    (hc : 1 < c) (hT : 0 ≤ T) :
    chapter06LeftVerticalIntegral (K := K) F c T =
      -chapter06RightVerticalIntegral (K := K) F c T := by
  sorry

theorem chapter06_contour_difference_is_twice_right_vertical
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c T : ℝ}
    (hc : 1 < c) (hT : 0 ≤ T) :
    chapter06RightVerticalIntegral (K := K) F c T -
        chapter06LeftVerticalIntegral (K := K) F c T =
      2 * chapter06RightVerticalIntegral (K := K) F c T := by
  rw [chapter06_left_vertical_integral_substitution K P hF hc hT]
  ring

theorem chapter06_contour_identity
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c T : ℝ}
    (hc : 1 < c) (hT : 0 ≤ T)
    (havoid : ∀ ρ : ℂ, ρ ∈ P.zeros.support →
      ρ.im ≠ T ∧ ρ.im ≠ -T) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (chapter06RightVerticalIntegral (K := K) F c T -
          chapter06LeftVerticalIntegral (K := K) F c T) =
      chapter06ContourResidueSum P.zeros F T +
        chapter06HorizontalError (K := K) F c T := by
  sorry

/-
SOURCE_NOTE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§6.2):
the source constructs the inverse-polynomial exponent and positive constant
in the displayed height-selection argument.  The Lean interface records that
data explicitly in `Chapter06ContourHeightSequence`.
-/
theorem chapter06_contour_height_sequence_available
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {c : ℝ} (hc : 1 < c) :
    ∃ H : Chapter06ContourHeightSequence K P.zeros c,
      Tendsto H.height atTop atTop := by
  exact ⟨P.contour_heights c hc, (P.contour_heights c hc).tendsToInfinity⟩

theorem chapter06_horizontal_error_tendsto_zero
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c)
    (H : Chapter06ContourHeightSequence K P.zeros c) :
    Tendsto (fun j => chapter06HorizontalError (K := K) F c (H.height j)) atTop
      (𝓝 0) := by
  sorry

theorem chapter06_contour_identity_along_admissible_heights
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c)
    (H : Chapter06ContourHeightSequence K P.zeros c) :
    ∀ᶠ j : ℕ in atTop,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
          (chapter06RightVerticalIntegral (K := K) F c (H.height j) -
            chapter06LeftVerticalIntegral (K := K) F c (H.height j)) =
        chapter06ContourResidueSum P.zeros F (H.height j) +
          chapter06HorizontalError (K := K) F c (H.height j) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
