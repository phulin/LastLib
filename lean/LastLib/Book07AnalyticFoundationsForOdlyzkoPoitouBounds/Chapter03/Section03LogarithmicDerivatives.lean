import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.3 Logarithmic derivatives -/

theorem chapter03_log_growth_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℝ, 1 ≤ q →
      Real.log q ≤ C * Real.rpow q (ε / 2) := by
  sorry

theorem chapter03_log_derivative_term_hasDerivAt
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (m : ℕ) {s : ℂ} :
    HasDerivAt (fun z : ℂ => chapter03EulerLogTerm P m z)
      (-(Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
        (chapter03PrimeIdealNorm P : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s)) s := by
  sorry

theorem chapter03_log_derivative_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      ‖chapter03LogDerivativeTerm q s‖) := by
  sorry

theorem chapter03_log_derivative_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K => chapter03LogDerivativeTerm q s) := by
  sorry

theorem chapter03_log_derivative_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => chapter03LogDerivativeTerm q s)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_log_derivative_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => ‖chapter03LogDerivativeTerm q s‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_log_derivative_nested_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun P : Chapter03PrimeIdeal K =>
        fun s : ℂ => ∑' m : ℕ, chapter03LogDerivativeTerm (P, m) s)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_log_derivative_formula
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta K) s) / chapter03DedekindZeta K s =
      chapter03LogDerivativeSeries K s := by
  sorry

theorem chapter03_log_derivative_formula_explicit
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta K) s) / chapter03DedekindZeta K s =
      ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ,
        (Real.log (chapter03PrimeIdealNorm P : ℝ) : ℂ) *
          (chapter03PrimeIdealNorm P : ℂ) ^
            (-((m + 1 : ℕ) : ℂ) * s) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
