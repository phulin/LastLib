import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section03ExactEvaluationOfTheArchimedeanTerms

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology

noncomputable section

/-! ## 8.4 Smoothing corners without changing the bound -/

def Chapter08ApproximateIdentity (η : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Integrable (η n)) ∧
    (∀ n, HasCompactSupport (η n)) ∧
    (∀ n, ContDiff ℝ ∞ (η n)) ∧
    (∀ n x, 0 ≤ η n x) ∧
    (∀ n x, η n (-x) = η n x) ∧
    (∀ n, ∫ x : ℝ, η n x = 1) ∧
    (∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)))

def chapter08SmoothedIntervalIndicator
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  chapter08Convolution (η n) (chapter08IntervalIndicator T)

def chapter08SmoothedUnconditionalTriangle
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  chapter08NormalizedAutocorrelation (chapter08SmoothedIntervalIndicator η T n)

def chapter08SmoothedUnconditionalTestFunction
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => chapter08SmoothedUnconditionalTriangle η T n x / Real.cosh (x / 2)

def Chapter08SmoothingIntegralConvergence
    (η : ℕ → ℝ → ℝ) (T : ℝ) : Prop :=
  Tendsto (fun n => chapter08A (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08A (chapter08FUnconditionalTriangle T))) ∧
    Tendsto (fun n => chapter08B (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08B (chapter08FUnconditionalTriangle T))) ∧
    Tendsto (fun n => chapter08C (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08C (chapter08FUnconditionalTriangle T)))

theorem chapter08_smoothed_autocorrelation_nonnegative
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T) :
    ∀ n x, 0 ≤ chapter08SmoothedUnconditionalTriangle η T n x := by
  sorry

theorem chapter08_smoothed_autocorrelation_positive_type
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T) :
    ∀ n, Chapter08PositiveType (chapter08SmoothedUnconditionalTriangle η T n) := by
  sorry

theorem chapter08_smoothed_unconditional_admissible
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T) :
    ∀ n, Chapter08UnconditionallyAdmissible
      (chapter08SmoothedUnconditionalTestFunction η T n) := by
  sorry

/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§8.4):
  “Approximate identities” and “converge in every integral above” do not specify the topology,
  support, normalization, or a dominating majorant.  The minimal principled correction is to
  require a compactly supported smooth even nonnegative mass-one sequence and to expose the
  three weighted integral convergences as `Chapter08SmoothingIntegralConvergence`. -/
theorem chapter08_smoothing_construction
    {T : ℝ} (hT : 0 < T) :
    ∃ η : ℕ → ℝ → ℝ,
      Chapter08ApproximateIdentity η ∧
        (∀ n, Chapter08UnconditionallyAdmissible
          (chapter08SmoothedUnconditionalTestFunction η T n)) ∧
        Chapter08SmoothingIntegralConvergence η T := by
  sorry

theorem chapter08_unconditional_triangle_near_zero
    {T : ℝ} (hT : 0 < T) :
    (fun x : ℝ =>
        1 - chapter08FUnconditionalTriangle T x - x / T) =O[nhdsWithin 0 (Ici 0)]
      (fun x : ℝ => x ^ 2) := by
  sorry

theorem chapter08_unconditional_triangle_B_integrand_tendsto
    {T : ℝ} (hT : 0 < T) :
    Tendsto
      (fun x : ℝ =>
        (1 - chapter08FUnconditionalTriangle T x) / (2 * Real.sinh (x / 2)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (1 / T)) := by
  sorry

theorem chapter08_dominated_convergence_transfers_lower_bound
    {K : Type*} [Field K] [NumberField K]
    (hK : 0 < Chapter08Degree K) {F : ℝ → ℝ} (u : ℕ → ℝ → ℝ)
    (hbound : ∀ n,
      Real.log (Chapter08RootDiscriminant K) ≥
        Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
          chapter08SignatureProportion K * (Real.pi / 2) -
          4 * chapter08A (u n) / (Chapter08Degree K : ℝ) -
          chapter08B (u n) -
          chapter08SignatureProportion K * chapter08C (u n))
    (hA : Tendsto (fun n => chapter08A (u n)) atTop (𝓝 (chapter08A F)))
    (hB : Tendsto (fun n => chapter08B (u n)) atTop (𝓝 (chapter08B F)))
    (hC : Tendsto (fun n => chapter08C (u n)) atTop (𝓝 (chapter08C F))) :
    Real.log (Chapter08RootDiscriminant K) ≥
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        chapter08SignatureProportion K * (Real.pi / 2) -
        4 * chapter08A F / (Chapter08Degree K : ℝ) -
        chapter08B F -
        chapter08SignatureProportion K * chapter08C F := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
