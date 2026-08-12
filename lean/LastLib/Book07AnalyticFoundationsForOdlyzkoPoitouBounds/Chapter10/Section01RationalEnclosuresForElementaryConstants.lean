import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## 10.1. Rational enclosures for elementary constants -/

def chapter10LogPartialSum (y : ℝ) (M : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range (M + 1),
    y ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

def chapter10LogRemainder (y : ℝ) (M : ℕ) : ℝ :=
  Real.log ((1 + y) / (1 - y)) - chapter10LogPartialSum y M

theorem chapter10_log_series_identity (y : ℝ) (M : ℕ) :
    Real.log ((1 + y) / (1 - y)) =
      chapter10LogPartialSum y M + chapter10LogRemainder y M := by
  sorry

theorem chapter10_log_series_remainder_bound
    {y : ℝ} (hy : |y| < 1) (M : ℕ) :
    |chapter10LogRemainder y M| ≤
      2 * |y| ^ (2 * M + 3) /
        (((2 * M + 3 : ℕ) : ℝ) * (1 - y ^ 2)) := by
  sorry

theorem chapter10_log_series_enclosure
    {y : ℝ} (hy : |y| < 1) (M : ℕ) :
    Real.log ((1 + y) / (1 - y)) =
        chapter10LogPartialSum y M + chapter10LogRemainder y M ∧
      |chapter10LogRemainder y M| ≤
        2 * |y| ^ (2 * M + 3) /
          (((2 * M + 3 : ℕ) : ℝ) * (1 - y ^ 2)) := by
  sorry

/- The range-reduction datum makes the phrase “any rational logarithm” precise: the argument
   must be positive, and the reduced parameter must lie in the convergence interval. -/
structure Chapter10PowerTwoReduction where
  argument : ℝ
  exponent : ℤ
  parameter : ℝ
  argument_pos : 0 < argument
  parameter_mem : |parameter| < 1
  representation :
    argument = (2 : ℝ) ^ exponent * ((1 + parameter) / (1 - parameter))

theorem chapter10_log_power_two_reduction
    (R : Chapter10PowerTwoReduction) :
    Real.log R.argument =
      (R.exponent : ℝ) * Real.log 2 +
        Real.log ((1 + R.parameter) / (1 - R.parameter)) := by
  sorry

theorem chapter10_positive_rational_has_power_two_reduction
    (q : ℚ) (hq : 0 < q) :
    ∃ k : ℤ, ∃ y : ℚ,
      |y| < 1 ∧
        q = (2 : ℚ) ^ k * ((1 + y) / (1 - y)) := by
  sorry

theorem chapter10_positive_rational_log_after_power_two_reduction
    {q : ℚ} (hq : 0 < q) {k : ℤ} {y : ℝ}
    (hy : |y| < 1)
    (hred : (q : ℝ) = (2 : ℝ) ^ k * ((1 + y) / (1 - y))) :
    Real.log (q : ℝ) =
      (k : ℝ) * Real.log 2 + Real.log ((1 + y) / (1 - y)) := by
  sorry

theorem chapter10_log_two_series_identity (M : ℕ) :
    Real.log 2 =
      chapter10LogPartialSum (1 / 3 : ℝ) M +
        chapter10LogRemainder (1 / 3 : ℝ) M := by
  sorry

theorem chapter10_log_two_series_remainder_bound (M : ℕ) :
    |chapter10LogRemainder (1 / 3 : ℝ) M| ≤
      2 * |(1 / 3 : ℝ)| ^ (2 * M + 3) /
        (((2 * M + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) := by
  sorry

def chapter10ArctanPartialSum (x : ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1),
    (-1 : ℝ) ^ j * x ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

def chapter10ArctanRemainder (x : ℝ) (M : ℕ) : ℝ :=
  Real.arctan x - chapter10ArctanPartialSum x M

def chapter10ArctanNextTerm (x : ℝ) (M : ℕ) : ℝ :=
  x ^ (2 * (M + 1) + 1) / ((2 * (M + 1) + 1 : ℕ) : ℝ)

theorem chapter10_arctan_series_identity (x : ℝ) (M : ℕ) :
    Real.arctan x =
      chapter10ArctanPartialSum x M + chapter10ArctanRemainder x M := by
  sorry

theorem chapter10_arctan_alternating_remainder_bound
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (M : ℕ) :
    0 ≤ (-1 : ℝ) ^ (M + 1) * chapter10ArctanRemainder x M ∧
      (-1 : ℝ) ^ (M + 1) * chapter10ArctanRemainder x M ≤
        chapter10ArctanNextTerm x M := by
  sorry

theorem chapter10_machin_formula :
    Real.pi =
      16 * Real.arctan (1 / 5 : ℝ) - 4 * Real.arctan (1 / 239 : ℝ) := by
  sorry

def chapter10BernoulliPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (bernoulli k : ℝ) * x ^ (n - k)

def chapter10PeriodicBernoulli (n : ℕ) (x : ℝ) : ℝ :=
  chapter10BernoulliPolynomial n (Int.fract x)

def chapter10BernoulliPolynomial8 (x : ℝ) : ℝ :=
  x ^ 8 - 4 * x ^ 7 + (14 / 3 : ℝ) * x ^ 6 -
    (7 / 3 : ℝ) * x ^ 4 + (2 / 3 : ℝ) * x ^ 2 - 1 / 30

def chapter10PeriodicBernoulli8 (x : ℝ) : ℝ :=
  chapter10BernoulliPolynomial8 (Int.fract x)

theorem chapter10_periodic_bernoulli_eq_floor (n : ℕ) (x : ℝ) :
    chapter10PeriodicBernoulli n x =
      chapter10BernoulliPolynomial n (x - (Int.floor x : ℝ)) := by
  sorry

theorem chapter10_periodic_bernoulli8_eq_floor (x : ℝ) :
    chapter10PeriodicBernoulli8 x =
      chapter10BernoulliPolynomial8 (x - (Int.floor x : ℝ)) := by
  sorry

def chapter10B2 : ℚ := 1 / 6

def chapter10B4 : ℚ := -1 / 30

def chapter10B6 : ℚ := 1 / 42

theorem chapter10_bernoulli_number_values :
    chapter10B2 = bernoulli 2 ∧
      chapter10B4 = bernoulli 4 ∧
        chapter10B6 = bernoulli 6 := by
  sorry

theorem chapter10_bernoulli_polynomial_eight_eq_displayed :
    chapter10BernoulliPolynomial 8 = chapter10BernoulliPolynomial8 := by
  sorry

theorem chapter10_bernoulli_polynomial_derivative
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    HasDerivAt (chapter10BernoulliPolynomial n)
      ((n : ℝ) * chapter10BernoulliPolynomial (n - 1) x) x := by
  sorry

theorem chapter10_periodic_bernoulli_derivative_on_unit_interval
    {n : ℕ} (hn : 0 < n) (m : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1)) :
    HasDerivAt (chapter10PeriodicBernoulli n)
      ((n : ℝ) * chapter10PeriodicBernoulli (n - 1) x) x := by
  sorry

theorem chapter10_bernoulli8_abs_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |chapter10BernoulliPolynomial8 x| ≤ (1 / 30 : ℝ) := by
  sorry

theorem chapter10_bernoulli8_abs_eq_only_at_endpoints
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (heq : |chapter10BernoulliPolynomial8 x| = (1 / 30 : ℝ)) :
    x = 0 ∨ x = 1 := by
  sorry

theorem chapter10_periodic_bernoulli8_abs_le (x : ℝ) :
    |chapter10PeriodicBernoulli8 x| ≤ (1 / 30 : ℝ) := by
  sorry

def chapter10Harmonic (N : ℕ) : ℝ :=
  (harmonic N : ℝ)

def chapter10EulerMaclaurinMainTerm (N : ℕ) : ℝ :=
  chapter10Harmonic N - Real.log (N : ℝ) - 1 / (2 * (N : ℝ)) +
    1 / (12 * (N : ℝ) ^ 2) - 1 / (120 * (N : ℝ) ^ 4) +
      1 / (252 * (N : ℝ) ^ 6)

def chapter10EulerMascheroniRemainder (N : ℕ) : ℝ :=
  Real.eulerMascheroniConstant - chapter10EulerMaclaurinMainTerm N

def chapter10Bernoulli8IntegralRemainder (N : ℕ) : ℝ :=
  ∫ x in Set.Ioi (N : ℝ), chapter10PeriodicBernoulli8 x / x ^ 9

def chapter10SignedBernoulli8IntegralRemainder (N : ℕ) (ε : ℝ) : ℝ :=
  ε * chapter10Bernoulli8IntegralRemainder N

theorem chapter10_inverse_ninth_power_tail_integral
    {N : ℕ} (hN : 0 < N) :
    (∫ x in Set.Ioi (N : ℝ), 1 / x ^ 9) =
      1 / (8 * (N : ℝ) ^ 8) := by
  sorry

theorem chapter10_euler_mascheroni_expansion (N : ℕ) :
    Real.eulerMascheroniConstant =
      chapter10EulerMaclaurinMainTerm N + chapter10EulerMascheroniRemainder N := by
  sorry

theorem chapter10_euler_mascheroni_remainder_signed_integral
    {N : ℕ} (hN : 0 < N) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      chapter10EulerMascheroniRemainder N =
        chapter10SignedBernoulli8IntegralRemainder N ε := by
  sorry

theorem chapter10_euler_mascheroni_remainder_bound
    {N : ℕ} (hN : 0 < N) :
    |chapter10EulerMascheroniRemainder N| <
      1 / (240 * (N : ℝ) ^ 8) := by
  sorry

/- The decimals in (10.4) are represented by named rational endpoints so that later ledgers can
   reuse them as exact data rather than as floating-point notation. -/
def chapter10GammaLower : ℚ := 577215664901532 / 10 ^ 15

def chapter10GammaUpper : ℚ := 577215664901533 / 10 ^ 15

def chapter10PiLower : ℚ := 3141592653589793 / 10 ^ 15

def chapter10PiUpper : ℚ := 3141592653589794 / 10 ^ 15

/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§10.1, (10.4)):
  the sentence preceding the displayed enclosure cites only (10.1)--(10.2), although the
  enclosure for `γ` also depends on the Euler--Maclaurin formula and remainder in (10.3).  The
  smallest correction is to cite (10.3) for the `γ` bound as well. -/
theorem chapter10_gamma_directed_bounds :
    (chapter10GammaLower : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (chapter10GammaUpper : ℝ) := by
  sorry

theorem chapter10_pi_directed_bounds :
    (chapter10PiLower : ℝ) < Real.pi ∧
      Real.pi < (chapter10PiUpper : ℝ) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
