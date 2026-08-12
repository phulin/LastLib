import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.2 Euler products -/

theorem chapter03_euler_product_eq_dedekind_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s = chapter03EulerProduct K s := by
  sorry

theorem chapter03_euler_factor_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerFactor P s ≠ 0 := by
  sorry

theorem chapter03_euler_product_multipliable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Multipliable (fun P : Chapter03PrimeIdeal K => chapter03EulerFactor P s) := by
  sorry

theorem chapter03_euler_product_hasProd
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    HasProd (fun P : Chapter03PrimeIdeal K => chapter03EulerFactor P s)
      (chapter03DedekindZeta K s) := by
  sorry

theorem chapter03_euler_log_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      ‖chapter03EulerLogTerm q.1 q.2 s‖) := by
  sorry

theorem chapter03_euler_log_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun q : Chapter03PrimePower K =>
      chapter03EulerLogTerm q.1 q.2 s) := by
  sorry

theorem chapter03_euler_log_nested_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun P : Chapter03PrimeIdeal K =>
      ∑' m : ℕ, chapter03EulerLogTerm P m s) := by
  sorry

theorem chapter03_euler_log_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun q : Chapter03PrimePower K =>
        fun s : ℂ => ‖chapter03EulerLogTerm q.1 q.2 s‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_euler_log_series_eq_nested_sum
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter03EulerLogSeries K s =
      ∑' P : Chapter03PrimeIdeal K, ∑' m : ℕ, chapter03EulerLogTerm P m s := by
  rfl

theorem chapter03_euler_product_eq_exp_euler_log_series
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerProduct K s = Complex.exp (chapter03EulerLogSeries K s) := by
  sorry

theorem chapter03_euler_log_series_exponentiates_to_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Complex.exp (chapter03EulerLogSeries K s) = chapter03DedekindZeta K s := by
  sorry

theorem chapter03_dedekind_zeta_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s ≠ 0 := by
  sorry

theorem chapter03_euler_product_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03EulerProduct K s ≠ 0 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
