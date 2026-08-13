import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter NumberField
open scoped BigOperators Topology

/-! ### 6.3. Prime and discriminant terms -/

theorem chapter06_bilateral_laplace_inversion
    {F : ℝ → ℝ} (hF : Chapter06SmoothCompactSupport F)
    {c y : ℝ} (hc : 1 < c) (hy : 0 < y) :
    Tendsto (fun T => chapter06LaplaceInversePartial F c y T) atTop
      (𝓝 (F y : ℂ)) := by
  sorry

theorem chapter06_zeta_log_derivative_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun q : Chapter06PrimePower K =>
      ‖chapter06ZetaLogDerivativeTerm q s‖) := by
  sorry

theorem chapter06_zeta_log_derivative_series_eq
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06ZetaLogDerivative K s = chapter06ZetaLogDerivativeSeries K s := by
  sorry

theorem chapter06_zeta_log_derivative_negative_series_eq
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06LogDerivative
        (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.chapter03DedekindZeta K)
        s = -chapter06ZetaLogDerivativeSeries K s := by
  sorry

theorem chapter06_xi_log_derivative_decomposition
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : 1 < s.re) :
    chapter06LogDerivative (chapter06Xi K) s =
      chapter06PoleLogDerivative s + chapter06DiscriminantLogDerivative K +
        chapter06RealGammaLogDerivative K s +
        chapter06ComplexGammaLogDerivative K s -
        chapter06ZetaLogDerivative K s := by
  sorry

noncomputable def chapter06PrimeContourTermPartial
    {K : Type*} [Field K] [NumberField K]
    (q : Chapter06PrimePower K) (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        (-chapter06ZetaLogDerivativeTerm q
          (chapter06VerticalLinePoint c t)) * Complex.I)

theorem chapter06_prime_power_contour_inversion
    (K : Type*) [Field K] [NumberField K]
    (q : Chapter06PrimePower K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06PrimeContourTermPartial q F c T) atTop
      (𝓝 (-chapter06PrimePowerTerm F q)) := by
  sorry

noncomputable def chapter06ZetaPrimeContourPartial
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        (-chapter06ZetaLogDerivative K (chapter06VerticalLinePoint c t)) *
          Complex.I)

theorem chapter06_prime_contour_contribution
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06ZetaPrimeContourPartial K F c T) atTop
      (𝓝 (-(chapter06PrimeContribution K F) / 2)) := by
  sorry

noncomputable def chapter06DiscriminantContourPartial
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (c T : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (∫ t in (-T)..T,
      chapter06Phi F (chapter06VerticalLinePoint c t) *
        chapter06DiscriminantLogDerivative K * Complex.I)

theorem chapter06_discriminant_contour_contribution
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun T => chapter06DiscriminantContourPartial K F c T) atTop
      (𝓝 (chapter06DiscriminantLogDerivative K)) := by
  sorry

theorem chapter06_doubled_discriminant_contour_contribution
    (K : Type*) [Field K] [NumberField K] :
    2 * chapter06DiscriminantLogDerivative K =
      (Real.log (chapter06AbsoluteDiscriminant K) : ℂ) := by
  simp [chapter06DiscriminantLogDerivative]; ring

theorem chapter06_prime_power_term_nonzero_implies_log_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T)
    {q : Chapter06PrimePower K}
    (hq : chapter06PrimePowerTerm F q ≠ 0) :
    (q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T := by
  sorry

theorem chapter06_prime_power_term_nonzero_implies_norm_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T)
    {q : Chapter06PrimePower K}
    (hq : chapter06PrimePowerTerm F q ≠ 0) :
    Real.rpow (chapter06PrimeIdealNorm q.1 : ℝ) (q.2.1 : ℝ) ≤ Real.exp T := by
  sorry

theorem chapter06_prime_power_support_finite_of_support_within
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter06SupportWithin F T) :
    (chapter06PrimePowerSupport (K := K) F).Finite := by
  sorry

theorem chapter06_prime_power_term_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (q : Chapter06PrimePower K) :
    0 ≤ chapter06PrimePowerTerm F q := by
  sorry

noncomputable def chapter06FinitePrimePowerContribution
    {K : Type*} [Field K] [NumberField K]
    (F : ℝ → ℝ) (S : Finset (Chapter06PrimePower K)) : ℝ :=
  2 * ∑ q ∈ S, chapter06PrimePowerTerm F q

theorem chapter06_finite_prime_power_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter06PrimePower K)) :
    0 ≤ chapter06FinitePrimePowerContribution F S := by
  sorry

theorem chapter06_finite_prime_power_contribution_mono
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) {S T : Finset (Chapter06PrimePower K)}
    (hST : S ⊆ T) :
    chapter06FinitePrimePowerContribution F S ≤
      chapter06FinitePrimePowerContribution F T := by
  sorry

theorem chapter06_prime_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    (hFnonnegative : ∀ x, 0 ≤ F x) :
    0 ≤ chapter06PrimeContribution K F := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
