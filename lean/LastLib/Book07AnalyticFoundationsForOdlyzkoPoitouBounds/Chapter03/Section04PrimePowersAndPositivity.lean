import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

noncomputable section

open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors

/-! ### 3.4 Prime powers and positivity -/

theorem chapter03_prime_ideal_norm_ge_two
    (K : Type*) [Field K] [NumberField K] (P : Chapter03PrimeIdeal K) :
    2 ≤ chapter03PrimeIdealNorm P := by
  sorry

theorem chapter03_prime_ideal_log_norm_pos
    (K : Type*) [Field K] [NumberField K] (P : Chapter03PrimeIdeal K) :
    0 < Real.log (chapter03PrimeIdealNorm P : ℝ) := by
  sorry

theorem chapter03_weighted_prime_power_term_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (q : Chapter03PrimePower K) :
    0 ≤ chapter03WeightedPrimePowerTerm F q := by
  sorry

theorem chapter03_weighted_prime_power_sum_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter03PrimePower K)) :
    0 ≤ ∑ q ∈ S, chapter03WeightedPrimePowerTerm F q := by
  sorry

theorem chapter03_weighted_prime_power_tsum_nonneg
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x)
    (hsum : Summable (fun q : Chapter03PrimePower K =>
      chapter03WeightedPrimePowerTerm F q)) :
    0 ≤ ∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q := by
  sorry

theorem chapter03_weighted_prime_power_sum_mono
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) {S T : Finset (Chapter03PrimePower K)}
    (hST : S ⊆ T) :
    (∑ q ∈ S, chapter03WeightedPrimePowerTerm F q) ≤
      ∑ q ∈ T, chapter03WeightedPrimePowerTerm F q := by
  sorry

theorem chapter03_weighted_prime_power_partial_sum_le_full
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : ∀ x, 0 ≤ F x) (S : Finset (Chapter03PrimePower K))
    (hsum : Summable (fun q : Chapter03PrimePower K =>
      chapter03WeightedPrimePowerTerm F q)) :
    (∑ q ∈ S, chapter03WeightedPrimePowerTerm F q) ≤
      ∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q := by
  sorry

/-! The next interfaces record the residue-degree normalization behind the
prime-ideal examples. -/

def chapter03ResidueDegreeOverNatPrime
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (P : Ideal (𝓞 K)) : ℕ :=
  (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P

theorem chapter03_prime_ideal_norm_eq_prime_pow_residue_degree
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p) :
    Ideal.absNorm P = p ^ chapter03ResidueDegreeOverNatPrime p P := by
  sorry

theorem chapter03_euler_factors_are_indexed_by_prime_ideals
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter03EulerProduct K s =
      ∏' P : Chapter03PrimeIdeal K,
        (1 - (chapter03PrimeIdealNorm P : ℂ) ^ (-s))⁻¹ := by
  rfl

theorem chapter03_first_power_term_eq_log_derivative_zero_power
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter03PrimeIdeal K) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P.asIdeal s =
      chapter03LogDerivativeTerm (P, 0) s := by
  sorry

def chapter03RationalFirstPowerTerm (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s)

theorem chapter03_rational_example_log_derivative
    {s : ℂ} (hs : s ∈ chapter03EulerHalfPlane) :
    -(deriv (chapter03DedekindZeta ℚ) s) / chapter03DedekindZeta ℚ s =
      ∑' p : Nat.Primes, ∑' m : ℕ,
        (Real.log (p : ℝ) : ℂ) *
          (p : ℂ) ^ (-((m + 1 : ℕ) : ℂ) * s) := by
  sorry

theorem chapter03_rational_example_first_power_term
    (p : Nat.Primes) (s : ℂ) :
    chapter03RationalFirstPowerTerm p s =
      (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) := by
  rfl

theorem chapter03_log_norm_prime_square_eq_two_log_prime
    {p : ℕ} (hp : Nat.Prime p) :
    Real.log ((p ^ 2 : ℕ) : ℝ) = 2 * Real.log (p : ℝ) := by
  sorry

theorem chapter03_gaussian_split_prime_ideals
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) {p : ℕ} (hp : Nat.Prime p)
    (hmod : p % 4 = 1) :
    ∃ P Q : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      Q ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      P ≠ Q ∧
      Ideal.absNorm P = p ∧
      Ideal.absNorm Q = p ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(p : ℤ)} : Set ℤ)) = P * Q ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) p →
        R = P ∨ R = Q := by
  sorry

theorem chapter03_gaussian_inert_prime_ideal
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) {p : ℕ} (hp : Nat.Prime p)
    (hmod : p % 4 = 3) :
    ∃ P : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) p ∧
      Ideal.absNorm P = p ^ 2 ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(p : ℤ)} : Set ℤ)) = P ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) p → R = P := by
  sorry

theorem chapter03_gaussian_ramified_prime_ideal_at_two
    (K : Type*) [Field K] [NumberField K]
    (hK : chapter03IsGaussianField K) :
    ∃ P : Ideal (𝓞 K),
      P ∈ chapter03PrimeIdealsOverNatPrime (K := K) 2 ∧
      Ideal.absNorm P = 2 ∧
      Ideal.map (algebraMap ℤ (𝓞 K))
          (Ideal.span ({(2 : ℤ)} : Set ℤ)) = P ^ 2 ∧
      ∀ R, R ∈ chapter03PrimeIdealsOverNatPrime (K := K) 2 → R = P := by
  sorry

theorem chapter03_gaussian_split_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P Q : Ideal (𝓞 K)} (hP : Ideal.absNorm P = p)
    (hQ : Ideal.absNorm Q = p) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P s +
        chapter03FirstPowerPrimeIdealTerm Q s =
      2 * (Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-s) := by
  sorry

theorem chapter03_gaussian_inert_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : Nat.Prime p)
    {P : Ideal (𝓞 K)} (hP : Ideal.absNorm P = p ^ 2) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P s =
      (2 * (Real.log (p : ℝ) : ℂ)) * (p : ℂ) ^ (-((2 : ℂ) * s)) := by
  sorry

theorem chapter03_gaussian_ramified_first_power_contribution
    (K : Type*) [Field K] [NumberField K] {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = 2) (s : ℂ) :
    chapter03FirstPowerPrimeIdealTerm P s =
      (Real.log (2 : ℝ) : ℂ) * (2 : ℂ) ^ (-s) := by
  sorry

theorem chapter03_weighted_prime_power_nonzero_implies_bound
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T)
    {q : Chapter03PrimePower K}
    (hq : chapter03WeightedPrimePowerTerm F q ≠ 0) :
    (((q.2 + 1 : ℕ) : ℝ) *
        Real.log (chapter03PrimeIdealNorm q.1 : ℝ)) ≤ T := by
  sorry

theorem chapter03_weighted_prime_power_support_finite
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    {q : Chapter03PrimePower K |
      chapter03WeightedPrimePowerTerm F q ≠ 0}.Finite := by
  sorry

noncomputable def chapter03PrimePowerLedger
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    Finset (Chapter03PrimePower K) :=
  (chapter03_weighted_prime_power_support_finite (K := K) hT hF).toFinset

theorem chapter03_mem_prime_power_ledger_iff
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T)
    (q : Chapter03PrimePower K) :
    q ∈ chapter03PrimePowerLedger K F T hT hF ↔
      chapter03WeightedPrimePowerTerm F q ≠ 0 := by
  sorry

theorem chapter03_weighted_prime_power_tsum_eq_ledger_sum
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hF : chapter03SupportWithin F T) :
    (∑' q : Chapter03PrimePower K, chapter03WeightedPrimePowerTerm F q) =
      ∑ q ∈ chapter03PrimePowerLedger K F T hT hF,
        chapter03WeightedPrimePowerTerm F q := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
