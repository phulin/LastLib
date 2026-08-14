import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

/-! ### 6.2. The truncated contour identity -/

theorem chapter06_contour_rectangle_mem_iff
    {c T : ℝ} {z : ℂ} :
    z ∈ chapter06ContourRectangle c T ↔
      1 - c ≤ z.re ∧ z.re ≤ c ∧ |z.im| ≤ T := by
  rfl

theorem chapter06_phi_functional_equation_symmetry
    {F : ℝ → ℝ} (hF : Chapter06SmoothCompactSupport F) :
    ∀ s : ℂ, chapter06Phi F (1 - s) = chapter06Phi F s := by
  intro s
  change chapter05BilateralLaplaceTransform F (1 - s) =
    chapter05BilateralLaplaceTransform F s
  have hInt : ∀ z : ℂ,
      Integrable (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel z x) volume := by
    intro z
    have hFc : Continuous (fun x : ℝ => (F x : ℂ)) := by
      exact Complex.continuous_ofReal.comp hF.2.1.continuous
    have hkernel : Continuous (chapter05LaplaceKernel z) := by
      fun_prop [chapter05LaplaceKernel]
    have hcompact : HasCompactSupport (fun x : ℝ => (F x : ℂ)) := by
      simpa [Function.comp_def] using
        hF.2.2.comp_left (g := Complex.ofReal) (by simp)
    exact (hFc.mul hkernel).integrable_of_hasCompactSupport
      hcompact.mul_right
  simpa using (chapter05_laplace_reflection hF.1 hInt (1 - s))

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
  have hfun : chapter06Xi K = (fun z : ℂ => chapter06Xi K (1 - z)) := by
    funext z
    exact P.functional_equation z
  have hderiv := congrArg (fun g : ℂ → ℂ => deriv g s) hfun
  have hderiv' : deriv (chapter06Xi K) s =
      -deriv (chapter06Xi K) (1 - s) := by
    simpa only [deriv_comp_const_sub] using hderiv
  unfold chapter06LogDerivative
  field_simp [hs, hsym]
  rw [hderiv', P.functional_equation s]
  ring

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
  have _hc : 1 < c := hc
  have _hT : 0 ≤ T := hT
  have hlog (s : ℂ) :
      chapter06LogDerivative (chapter06Xi K) (1 - s) =
        -chapter06LogDerivative (chapter06Xi K) s := by
    by_cases hs : chapter06Xi K s = 0
    · have hs' : chapter06Xi K (1 - s) = 0 := by
        rw [← P.functional_equation s]
        exact hs
      simp [chapter06LogDerivative, hs, hs']
    · have hs' : chapter06Xi K (1 - s) ≠ 0 := by
        intro hs'
        apply hs
        rw [P.functional_equation s]
        exact hs'
      exact chapter06_xi_log_derivative_functional_equation K P hs hs'
  have hpoint (t : ℝ) :
      chapter06VerticalLinePoint (1 - c) t =
        1 - chapter06VerticalLinePoint c (-t) := by
    simp [chapter06VerticalLinePoint]
    ring
  have hcontour (t : ℝ) :
      chapter06ContourIntegrand (K := K) F
          (chapter06VerticalLinePoint (1 - c) t) =
        -chapter06ContourIntegrand (K := K) F
          (chapter06VerticalLinePoint c (-t)) := by
    rw [hpoint t]
    unfold chapter06ContourIntegrand
    rw [hlog]
    rw [chapter06_phi_functional_equation_symmetry hF]
    ring
  unfold chapter06LeftVerticalIntegral chapter06RightVerticalIntegral
  calc
    (∫ t in (-T)..T,
        chapter06ContourIntegrand (K := K) F
            (chapter06VerticalLinePoint (1 - c) t) * Complex.I) =
      ∫ t in (-T)..T,
        -(chapter06ContourIntegrand (K := K) F
            (chapter06VerticalLinePoint c (-t)) * Complex.I) := by
          apply intervalIntegral.integral_congr
          intro t ht
          simp only
          rw [hcontour t]
          ring
    _ = -∫ t in (-T)..T,
        chapter06ContourIntegrand (K := K) F
          (chapter06VerticalLinePoint c (-t)) * Complex.I := by
          rw [intervalIntegral.integral_neg]
      _ = -∫ t in (-T)..T,
        chapter06ContourIntegrand (K := K) F
          (chapter06VerticalLinePoint c t) * Complex.I := by
          congr 1
          simpa using
            (intervalIntegral.integral_comp_neg
              (f := fun t : ℝ =>
                chapter06ContourIntegrand (K := K) F
                  (chapter06VerticalLinePoint c t) * Complex.I)
              (a := -T) (b := T))

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
  filter_upwards [] with j
  apply chapter06_contour_identity K P hF hc (H.positive j).le ?_
  intro ρ hρ
  have hbase : 0 < H.separationConstant /
      Real.rpow (H.height j + 3) (H.separationExponent : ℝ) := by
    apply div_pos H.separationConstant_pos
    apply Real.rpow_pos_of_pos
    linarith [H.positive j]
  constructor
  · intro hEq
    have hsep := H.avoids_zero_ordinates j ρ hρ
    have hpos : 0 < |H.height j - ρ.im| :=
      lt_of_lt_of_le hbase hsep
    apply (ne_of_gt hpos)
    simp [hEq]
  · intro hEq
    have hρstar : star ρ ∈ P.zeros.support :=
      (P.zeros.conjugation_partner (ρ := ρ)).mp hρ
    have hsep := H.avoids_zero_ordinates j (star ρ) hρstar
    have hpos : 0 < |H.height j - (star ρ).im| :=
      lt_of_lt_of_le hbase hsep
    apply (ne_of_gt hpos)
    simp [hEq]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
