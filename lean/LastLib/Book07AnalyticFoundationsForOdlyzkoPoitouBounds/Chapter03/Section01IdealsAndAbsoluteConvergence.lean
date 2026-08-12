import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.1 Ideals and absolute convergence -/

theorem chapter03_prime_ideal_over_iff
    (K : Type*) [Field K] [NumberField K] {p : ℕ}
    (P : Chapter03PrimeIdeal K) :
    P.asIdeal ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ↔
      P.asIdeal.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  sorry

theorem chapter03_prime_over_to_height_one
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    ∃ v : Chapter03PrimeIdeal K, v.asIdeal = P := by
  sorry

theorem chapter03_integral_ideals_bounded_norm_finite
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ B}.Finite := by
  exact Ideal.finite_setOfPred_absNorm_le B

theorem chapter03_nonzero_integral_ideals_bounded_norm_finite
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    {I : Chapter03IntegralIdeal K | chapter03IdealNorm I ≤ B}.Finite := by
  exact Ideal.finite_setOfPred_absNorm_le₀ B

theorem chapter03_nonzero_ideal_factorization
    (K : Type*) [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ P : Chapter03PrimeIdeal K, P.maxPowDividing I = I := by
  exact Ideal.finprod_heightOneSpectrum_factorization hI

theorem chapter03_prime_ideals_over_rational_prime_finite
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p) :
    (chapter03PrimeIdealsOverNatPrime (K := K) p).Finite := by
  sorry

theorem chapter03_prime_ideal_count_le_degree
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p) :
    (chapter03PrimeIdealsOverNatPrime (K := K) p).ncard ≤ chapter03Degree K := by
  sorry

theorem chapter03_prime_ideal_norm_ge_rational_prime
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    p ≤ Ideal.absNorm P := by
  sorry

theorem chapter03_real_euler_product_bound
    (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    chapter03RealEulerProduct K σ ≤
      chapter03RationalPrimeEulerProduct σ ^ chapter03Degree K := by
  sorry

theorem chapter03_rational_prime_euler_product_eq_riemann_zeta
    {σ : ℝ} (hσ : 1 < σ) :
    chapter03RationalPrimeEulerProduct σ = chapter03RiemannZetaOnReal σ := by
  sorry

theorem chapter03_rational_zeta_series_summable
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.rpow ((n : ℝ) + 1) (-σ)) := by
  sorry

theorem chapter03_ideal_series_eq_dedekind_zeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    chapter03DedekindZeta K s = chapter03IdealSeries K s := by
  sorry

theorem chapter03_ideal_series_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun I : Chapter03IntegralIdeal K => chapter03IdealTerm s I) := by
  sorry

theorem chapter03_ideal_series_absolutely_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    Summable (fun I : Chapter03IntegralIdeal K => ‖chapter03IdealTerm s I‖) := by
  sorry

theorem chapter03_ideal_series_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => chapter03IdealTerm s I)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_ideal_series_norm_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => ‖chapter03IdealTerm s I‖)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_ideal_series_derivative_summable_uniformly_on
    (K : Type*) [Field K] [NumberField K] (ε : ℝ) (hε : 0 < ε) :
    SummableUniformlyOn
      (fun I : Chapter03IntegralIdeal K =>
        fun s : ℂ => chapter03IdealTermDerivative s I)
      (chapter03EulerHalfPlaneClosed ε) := by
  sorry

theorem chapter03_euler_half_plane_isOpen :
    IsOpen chapter03EulerHalfPlane := by
  sorry

theorem chapter03_euler_half_plane_closed_subset
    {ε : ℝ} (hε : 0 < ε) :
    chapter03EulerHalfPlaneClosed ε ⊆ chapter03EulerHalfPlane := by
  sorry

theorem chapter03_ideal_term_hasDerivAt
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter03IntegralIdeal K) (s : ℂ) :
    HasDerivAt (fun z : ℂ => chapter03IdealTerm z I)
      (chapter03IdealTermDerivative s I) s := by
  sorry

theorem chapter03_dedekind_zeta_differentiableOn
    (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (chapter03DedekindZeta K) chapter03EulerHalfPlane := by
  sorry

theorem chapter03_dedekind_zeta_hasDerivAt_of_euler_half_plane
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s ∈ chapter03EulerHalfPlane) :
    HasDerivAt (chapter03DedekindZeta K)
      (∑' I : Chapter03IntegralIdeal K, chapter03IdealTermDerivative s I) s := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
