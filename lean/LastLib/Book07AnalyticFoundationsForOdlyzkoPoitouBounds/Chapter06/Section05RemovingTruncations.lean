import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! ### 6.5. Removing the truncations -/

theorem chapter06_basic_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  sorry

theorem chapter06_zero_count_unit_band
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter06ZeroBandCount Z T : ℕ) : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  exact Z.unit_band_bound

theorem chapter06_zero_count_increment_bound
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      (chapter06ZeroBandCount Z T : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  sorry

theorem chapter06_smooth_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  sorry

theorem chapter06_zero_partial_sum_tendsto
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  sorry

theorem chapter06_basic_zero_sum_is_symmetric_limit
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  exact chapter06_zero_partial_sum_tendsto K Z hF hT

theorem chapter06_symmetric_zero_value_independent_of_heights
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T U : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hU : Tendsto U atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n) -
      chapter06ZeroPartialSum Z F (U n)) atTop (𝓝 0) := by
  sorry

/-
SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§6.5):
“smooth by even convolution with a nonnegative compactly supported approximate
identity, then correct the value at zero by a factor tending to one” leaves
the topology, mass normalization, concentration property, and correction
factor unspecified.  The minimal usable interface is
`chapter06ApproximateIdentity` together with the explicit smoothed functions
and origin-correction factor below.
-/
theorem chapter06_approximate_identity_exists :
    ∃ η : ℕ → ℝ → ℝ, chapter06ApproximateIdentity η := by
  sorry

theorem chapter06_origin_correction_factor_apply_zero
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ)
    (h : chapter06SmoothedConvolution η F n 0 ≠ 0) :
    chapter06SmoothedTestFunction η F n 0 = 1 := by
  sorry

theorem chapter06_smoothed_origin_eventually_nonzero
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop,
      chapter06SmoothedConvolution η F n 0 ≠ 0 := by
  sorry

theorem chapter06_origin_correction_factor_tendsto_one
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) := by
  sorry

theorem chapter06_smoothed_test_functions_basic_admissible
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop, Chapter06BasicallyAdmissible
      (chapter06SmoothedTestFunction η F n) := by
  sorry

theorem chapter06_smoothed_test_functions_smooth_compact
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ n, Chapter06SmoothCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
  sorry

theorem chapter06_smoothed_test_functions_decay_uniformly
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ σ t : ℝ,
      |σ| ≤ R →
        ‖chapter06Phi (chapter06SmoothedTestFunction η F n)
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2 := by
  sorry

theorem chapter06_smoothed_zero_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06SymmetricZeroSum Z
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  sorry

theorem chapter06_smoothed_prime_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06PrimeContribution K
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06PrimeContribution K F)) := by
  sorry

theorem chapter06_smoothed_archimedean_terms_converge
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06A (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06A F)) ∧
      Tendsto (fun n => chapter06B (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06B F)) ∧
      Tendsto (fun n => chapter06C (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06C F)) := by
  sorry

theorem chapter06_universal_expression_eq_formula_without_sums
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) :
    chapter06ExplicitFormulaRightHandSide K Z F -
        chapter06ZeroContribution Z F - chapter06PrimeContribution K F =
      chapter06UniversalLowerBoundExpression K F := by
  simp [chapter06ExplicitFormulaRightHandSide,
    chapter06UniversalLowerBoundExpression]; ring

theorem chapter06_universal_expression_congr_of_ae
    (K : Type*) [Field K] [NumberField K] {F G : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    (hG : Chapter06BasicallyAdmissible G)
    (hFG : F =ᵐ[volume] G) :
    chapter06UniversalLowerBoundExpression K F =
      chapter06UniversalLowerBoundExpression K G := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
