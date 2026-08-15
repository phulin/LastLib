import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Dependencies
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.NumberTheory.BernoulliPolynomials

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open MeasureTheory Set
open Filter
open scoped BigOperators Topology

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
  simp [chapter10LogRemainder, chapter10LogPartialSum]

theorem chapter10_log_series_remainder_bound
    {y : ℝ} (hy : |y| < 1) (M : ℕ) :
    |chapter10LogRemainder y M| ≤
      2 * |y| ^ (2 * M + 3) /
        (((2 * M + 3 : ℕ) : ℝ) * (1 - y ^ 2)) := by
  let f : ℕ → ℝ := fun k ↦
    (2 : ℝ) * (1 / ((2 * k + 1 : ℕ) : ℝ)) * y ^ (2 * k + 1)
  let k : ℕ := M + 1
  have hsum : HasSum f (Real.log (1 + y) - Real.log (1 - y)) := by
    simpa [f] using Real.hasSum_log_sub_log_of_abs_lt_one hy
  have hsplit := hsum.summable.sum_add_tsum_nat_add k
  have htail : (∑' i : ℕ, f (i + k)) = chapter10LogRemainder y M := by
    have hlog : (∑' i : ℕ, f i) = Real.log (1 + y) - Real.log (1 - y) :=
      hsum.tsum_eq
    have hfinite : (∑ i ∈ Finset.range k, f i) = chapter10LogPartialSum y M := by
      dsimp [f, k]
      unfold chapter10LogPartialSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hquot : Real.log ((1 + y) / (1 - y)) =
        Real.log (1 + y) - Real.log (1 - y) := by
      rw [Real.log_div]
      · linarith [abs_lt.mp hy |>.1]
      · linarith [abs_lt.mp hy |>.2]
    calc
      (∑' i : ℕ, f (i + k)) = (∑' i : ℕ, f i) - ∑ i ∈ Finset.range k, f i := by
        linarith [hsplit]
      _ = (Real.log (1 + y) - Real.log (1 - y)) -
          chapter10LogPartialSum y M := by rw [hlog, hfinite]
      _ = chapter10LogRemainder y M := by
        rw [← hquot]
        rfl
  let a : ℝ := |y|
  let r : ℝ := a ^ 2
  let c : ℝ := 2 * a ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
  let g : ℕ → ℝ := fun i ↦ c * r ^ i
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact abs_nonneg y
  have ha1 : a < 1 := by
    dsimp [a]
    exact hy
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    have hprod : 0 < (1 - a) * (1 + a) := by positivity
    dsimp [r]
    nlinarith [hprod]
  have hgeom : HasSum g (c * (1 - r)⁻¹) := by
    simpa [g] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left c
  have hbound : ∀ i : ℕ, ‖f (i + k)‖ ≤ g i := by
    intro i
    have hki : 2 * k + 1 ≤ 2 * (i + k) + 1 := by omega
    have hden : ((2 * k + 1 : ℕ) : ℝ) ≤
        ((2 * (i + k) + 1 : ℕ) : ℝ) := by exact_mod_cast hki
    have hden_pos : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hinv : 1 / ((2 * (i + k) + 1 : ℕ) : ℝ) ≤
        1 / ((2 * k + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hden_pos hden
    have hpow : |y| ^ (2 * (i + k) + 1) =
        |y| ^ (2 * k + 1) * (|y| ^ 2) ^ i := by
      rw [show 2 * (i + k) + 1 = (2 * k + 1) + 2 * i by omega,
        pow_add, ← pow_mul]
    calc
      ‖f (i + k)‖ =
          2 * (1 / ((2 * (i + k) + 1 : ℕ) : ℝ)) *
            |y| ^ (2 * (i + k) + 1) := by
        dsimp [f]
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num),
          abs_of_nonneg (by positivity), abs_pow]
      _ ≤ 2 * (1 / ((2 * k + 1 : ℕ) : ℝ)) *
            |y| ^ (2 * (i + k) + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv (by positivity)) (by positivity)
      _ = g i := by
        dsimp [g, c, r, a]
        rw [hpow]
        ring
  have hshift : Summable (fun i : ℕ ↦ f (i + k)) :=
    hsum.summable.comp_injective (add_left_injective k)
  have hnorm₀ : |∑' i : ℕ, f (i + k)| ≤ c * (1 - r)⁻¹ := by
    have h := hshift.hasSum.norm_le_of_bounded hgeom hbound
    simpa only [Real.norm_eq_abs] using h
  calc
    |chapter10LogRemainder y M| = |∑' i : ℕ, f (i + k)| := by rw [htail]
    _ ≤ c * (1 - r)⁻¹ := hnorm₀
    _ = 2 * |y| ^ (2 * M + 3) /
        (((2 * M + 3 : ℕ) : ℝ) * (1 - y ^ 2)) := by
      have hy2 : 1 - y ^ 2 ≠ 0 := by
        have hprod : 0 < (1 - |y|) * (1 + |y|) := by positivity
        exact ne_of_gt (by nlinarith [hprod, sq_abs y])
      dsimp [c, r, a, k]
      rw [sq_abs y]
      field_simp [hy2]
      ring_nf

theorem chapter10_log_series_enclosure
    {y : ℝ} (hy : |y| < 1) (M : ℕ) :
    Real.log ((1 + y) / (1 - y)) =
        chapter10LogPartialSum y M + chapter10LogRemainder y M ∧
      |chapter10LogRemainder y M| ≤
        2 * |y| ^ (2 * M + 3) /
          (((2 * M + 3 : ℕ) : ℝ) * (1 - y ^ 2)) := by
  exact ⟨chapter10_log_series_identity y M,
    chapter10_log_series_remainder_bound hy M⟩

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
  have hpow : 0 < (2 : ℝ) ^ R.exponent := zpow_pos (by norm_num) _
  have hprod : 0 < (2 : ℝ) ^ R.exponent *
      ((1 + R.parameter) / (1 - R.parameter)) := by
    rw [← R.representation]
    exact R.argument_pos
  have hfrac : 0 < (1 + R.parameter) / (1 - R.parameter) := by
    rcases (mul_pos_iff.mp hprod) with ⟨_, hb⟩ | ⟨ha, _⟩
    · exact hb
    · linarith
  rw [R.representation, Real.log_mul (ne_of_gt hpow) (ne_of_gt hfrac), Real.log_zpow]

theorem chapter10_positive_rational_has_power_two_reduction
    (q : ℚ) (hq : 0 < q) :
    ∃ k : ℤ, ∃ y : ℚ,
      |y| < 1 ∧
        q = (2 : ℚ) ^ k * ((1 + y) / (1 - y)) := by
  refine ⟨0, (q - 1) / (q + 1), ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by linarith : 0 < q + 1)]
    rw [div_lt_one (by linarith : 0 < q + 1)]
    exact (abs_lt).2 ⟨by linarith, by linarith⟩
  · norm_num
    field_simp
    ring

theorem chapter10_positive_rational_log_after_power_two_reduction
    {q : ℚ} (hq : 0 < q) {k : ℤ} {y : ℝ}
    (hy : |y| < 1)
    (hred : (q : ℝ) = (2 : ℝ) ^ k * ((1 + y) / (1 - y))) :
    Real.log (q : ℝ) =
      (k : ℝ) * Real.log 2 + Real.log ((1 + y) / (1 - y)) := by
  exact chapter10_log_power_two_reduction
    { argument := (q : ℝ)
      exponent := k
      parameter := y
      argument_pos := by exact_mod_cast hq
      parameter_mem := hy
      representation := hred }

theorem chapter10_log_two_series_identity (M : ℕ) :
    Real.log 2 =
      chapter10LogPartialSum (1 / 3 : ℝ) M +
        chapter10LogRemainder (1 / 3 : ℝ) M := by
  convert chapter10_log_series_identity (1 / 3 : ℝ) M using 1; norm_num

theorem chapter10_log_two_series_remainder_bound (M : ℕ) :
    |chapter10LogRemainder (1 / 3 : ℝ) M| ≤
      2 * |(1 / 3 : ℝ)| ^ (2 * M + 3) /
        (((2 * M + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) := by
  exact chapter10_log_series_remainder_bound (by norm_num) M

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
  simp [chapter10ArctanRemainder, chapter10ArctanPartialSum]

theorem chapter10_arctan_alternating_remainder_bound
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (M : ℕ) :
    0 ≤ (-1 : ℝ) ^ (M + 1) * chapter10ArctanRemainder x M ∧
      (-1 : ℝ) ^ (M + 1) * chapter10ArctanRemainder x M ≤
        chapter10ArctanNextTerm x M := by
  let f : ℕ → ℝ := fun n ↦ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hx2 : x ^ 2 ≤ 1 := by
      have hprod : 0 ≤ x * (1 - x) :=
        mul_nonneg hx0 (sub_nonneg.mpr hx1)
      nlinarith [hprod]
    have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hx0 (2 * n + 1)) hx2
    have hden : ((2 * n + 1 : ℕ) : ℝ) ≤
        ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * n + 1 ≤ 2 * (n + 1) + 1 by omega)
    have hinv : 1 / ((2 * (n + 1) + 1 : ℕ) : ℝ) ≤
        1 / ((2 * n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hden
    dsimp [f]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    simpa only [one_div] using
      (mul_le_mul hpow hinv (by positivity) (by positivity))
  have hlim : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i) atTop
      (𝓝 (Real.arctan x)) := by
    by_cases hxlt : x < 1
    · have hnorm : ‖x‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx0]
        exact hxlt
      convert (Real.hasSum_arctan hnorm).tendsto_sum_nat using 1
      funext n
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      ring
    · have hxeq : x = 1 := le_antisymm hx1 (le_of_not_gt hxlt)
      subst x
      convert Real.tendsto_sum_pi_div_four using 1
      · funext n
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [f]
        simp only [one_pow]
        norm_num [Nat.cast_add, Nat.cast_mul]
        rw [div_eq_mul_inv]
      · rw [Real.arctan_one]
  obtain hM | hM := Nat.even_or_odd M
  · obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hM
    have hP : (∑ i ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ i * f i) =
        chapter10ArctanPartialSum x (2 * m) := by
      unfold chapter10ArctanPartialSum
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      ring
    have hupper := hanti.tendsto_le_alternating_series hlim m
    rw [hP] at hupper
    have hlower := hanti.alternating_series_le_tendsto hlim (m + 1)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.sum_range_succ] at hlower
    have hnext : f (2 * m + 1) = chapter10ArctanNextTerm x (2 * m) := by
      rfl
    have hterm : (-1 : ℝ) ^ (2 * m + 1) * f (2 * m + 1) =
        -chapter10ArctanNextTerm x (2 * m) := by
      rw [show (-1 : ℝ) ^ (2 * m + 1) = -1 by simp [pow_succ, pow_mul], hnext]
      ring
    rw [hP, hterm] at hlower
    dsimp [chapter10ArctanRemainder]
    rw [show (-1 : ℝ) ^ (2 * m + 1) = -1 by simp [pow_succ, pow_mul]]
    constructor <;> linarith
  · obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp hM
    have hP : (∑ i ∈ Finset.range (2 * (m + 1)), (-1 : ℝ) ^ i * f i) =
        chapter10ArctanPartialSum x (2 * m + 1) := by
      unfold chapter10ArctanPartialSum
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      ring
    have hlower := hanti.alternating_series_le_tendsto hlim (m + 1)
    rw [hP] at hlower
    have hupper := hanti.tendsto_le_alternating_series hlim (m + 1)
    rw [Finset.sum_range_succ] at hupper
    have hnext : f (2 * (m + 1)) = chapter10ArctanNextTerm x (2 * m + 1) := by
      rfl
    have hterm : (-1 : ℝ) ^ (2 * (m + 1)) * f (2 * (m + 1)) =
        chapter10ArctanNextTerm x (2 * m + 1) := by
      rw [show (-1 : ℝ) ^ (2 * (m + 1)) = 1 by simp [pow_mul], hnext]
      ring
    rw [hP, hterm] at hupper
    dsimp [chapter10ArctanRemainder]
    rw [show (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 by simp [pow_succ, pow_mul]]
    constructor <;> linarith

theorem chapter10_machin_formula :
    Real.pi =
      16 * Real.arctan (1 / 5 : ℝ) - 4 * Real.arctan (1 / 239 : ℝ) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [div_eq_mul_inv] at h ⊢
  linarith

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
  unfold chapter10PeriodicBernoulli
  rw [Int.self_sub_floor]

theorem chapter10_periodic_bernoulli8_eq_floor (x : ℝ) :
    chapter10PeriodicBernoulli8 x =
      chapter10BernoulliPolynomial8 (x - (Int.floor x : ℝ)) := by
  unfold chapter10PeriodicBernoulli8
  rw [Int.self_sub_floor]

def chapter10B2 : ℚ := 1 / 6

def chapter10B4 : ℚ := -1 / 30

def chapter10B6 : ℚ := 1 / 42

theorem chapter10_bernoulli_number_values :
    chapter10B2 = bernoulli 2 ∧
      chapter10B4 = bernoulli 4 ∧
        chapter10B6 = bernoulli 6 := by
  decide +kernel

theorem chapter10_bernoulli_polynomial_eight_eq_displayed :
    chapter10BernoulliPolynomial 8 = chapter10BernoulliPolynomial8 := by
  funext x
  have h0 : bernoulli 0 = 1 := by decide +kernel
  have h1 : bernoulli 1 = -1 / 2 := by decide +kernel
  have h2 : bernoulli 2 = 1 / 6 := by decide +kernel
  have h3 : bernoulli 3 = 0 := by decide +kernel
  have h4 : bernoulli 4 = -1 / 30 := by decide +kernel
  have h5 : bernoulli 5 = 0 := by decide +kernel
  have h6 : bernoulli 6 = 1 / 42 := by decide +kernel
  have h7 : bernoulli 7 = 0 := by decide +kernel
  have h8 : bernoulli 8 = -1 / 30 := by decide +kernel
  simp [chapter10BernoulliPolynomial, chapter10BernoulliPolynomial8,
    Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num [Nat.choose]
  ring

theorem chapter10_bernoulli_polynomial_derivative
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    HasDerivAt (chapter10BernoulliPolynomial n)
      ((n : ℝ) * chapter10BernoulliPolynomial (n - 1) x) x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfun : ∀ m : ℕ, chapter10BernoulliPolynomial m =
      (fun z : ℝ => Polynomial.aeval z (Polynomial.bernoulli m)) := by
    intro m
    funext z
    simp [chapter10BernoulliPolynomial, Polynomial.bernoulli]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have h := (Polynomial.bernoulli m.succ).hasDerivAt_aeval x
  rw [hfun m.succ]
  rw [Polynomial.derivative_bernoulli] at h
  rw [hfun (m.succ - 1)]
  simpa using h

theorem chapter10_periodic_bernoulli_derivative_on_unit_interval
    {n : ℕ} (hn : 0 < n) (m : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1)) :
    HasDerivAt (chapter10PeriodicBernoulli n)
      ((n : ℝ) * chapter10PeriodicBernoulli (n - 1) x) x := by
  have hfloor : (Int.floor x : ℝ) = (m : ℝ) :=
    Int.floor_eq_on_Ico' m x ⟨hx.1.le, hx.2⟩
  have hfract : Int.fract x = x - (m : ℝ) := by
    rw [← Int.self_sub_floor x, hfloor]
  have hev : (fun z : ℝ => chapter10PeriodicBernoulli n z) =ᶠ[𝓝 x]
      (fun z : ℝ => chapter10BernoulliPolynomial n (z - (m : ℝ))) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hx] with z hz
    have hfloor : (Int.floor z : ℝ) = (m : ℝ) :=
      Int.floor_eq_on_Ico' m z ⟨hz.1.le, hz.2⟩
    simp only [chapter10PeriodicBernoulli]
    rw [← Int.self_sub_floor z, hfloor]
  have hp :=
    (chapter10_bernoulli_polynomial_derivative hn (x - (m : ℝ))).comp x
      ((hasDerivAt_id x).sub_const (m : ℝ))
  have hp' := hp.congr_of_eventuallyEq hev
  have hmod : (Semiring.toModule : Module ℝ ℝ) =
      (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule := by
    apply Module.ext'
    intro r y
    simp [smul_eq_mul]
  cases hmod
  have hvalue : chapter10PeriodicBernoulli (n - 1) x =
      chapter10BernoulliPolynomial (n - 1) (x - (m : ℝ)) := by
    unfold chapter10PeriodicBernoulli
    rw [hfract]
  rw [hvalue]
  simpa only [Function.comp_def, mul_one] using hp'

theorem chapter10_bernoulli8_abs_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |chapter10BernoulliPolynomial8 x| ≤ (1 / 30 : ℝ) := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  apply (abs_le).2
  constructor
  · have hA : 0 ≤ 3 * x ^ 2 * (x - 1) ^ 2 := by positivity
    have hB : 0 ≤ 4 * x * (1 - x) := by positivity
    have hR : 0 ≤ 3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2 := by
      nlinarith [hA, hB]
    have hfactor : chapter10BernoulliPolynomial8 x + 1 / 30 =
        x ^ 2 * (1 - x) ^ 2 / 3 *
          (3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2) := by
      rw [chapter10BernoulliPolynomial8]
      ring
    have hleft : 0 ≤ x ^ 2 * (1 - x) ^ 2 / 3 := by positivity
    have hnonneg : 0 ≤ x ^ 2 * (1 - x) ^ 2 / 3 *
        (3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2) :=
      mul_nonneg hleft hR
    rw [← hfactor] at hnonneg
    linarith
  · let t : ℝ := x * (1 - x)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have ht1 : t ≤ (1 / 4 : ℝ) := by
      dsimp [t]
      nlinarith [sq_nonneg (2 * x - 1)]
    have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      pow_le_pow_left₀ ht0 ht1 2
    have ht3 : t ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ ht0 ht1 3
    have ht4 : t ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ ht0 ht1 4
    have hform : chapter10BernoulliPolynomial8 x =
        t ^ 4 + (4 / 3 : ℝ) * t ^ 3 + (2 / 3 : ℝ) * t ^ 2 - 1 / 30 := by
      dsimp [t]
      rw [chapter10BernoulliPolynomial8]
      ring
    rw [hform]
    nlinarith [ht2, ht3, ht4]

theorem chapter10_bernoulli8_abs_eq_only_at_endpoints
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (heq : |chapter10BernoulliPolynomial8 x| = (1 / 30 : ℝ)) :
    x = 0 ∨ x = 1 := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have hupper : chapter10BernoulliPolynomial8 x < (1 / 30 : ℝ) := by
    let t : ℝ := x * (1 - x)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have ht1 : t ≤ (1 / 4 : ℝ) := by
      dsimp [t]
      nlinarith [sq_nonneg (2 * x - 1)]
    have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
      pow_le_pow_left₀ ht0 ht1 2
    have ht3 : t ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ ht0 ht1 3
    have ht4 : t ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ ht0 ht1 4
    have hform : chapter10BernoulliPolynomial8 x =
        t ^ 4 + (4 / 3 : ℝ) * t ^ 3 + (2 / 3 : ℝ) * t ^ 2 - 1 / 30 := by
      dsimp [t]
      rw [chapter10BernoulliPolynomial8]
      ring
    rw [hform]
    nlinarith [ht2, ht3, ht4]
  have hsq : |chapter10BernoulliPolynomial8 x| ^ 2 =
      chapter10BernoulliPolynomial8 x ^ 2 := sq_abs _
  rw [heq] at hsq
  have hroots : chapter10BernoulliPolynomial8 x = (1 / 30 : ℝ) ∨
      chapter10BernoulliPolynomial8 x = -(1 / 30 : ℝ) := by
    have hfactor :
        (chapter10BernoulliPolynomial8 x - 1 / 30) *
            (chapter10BernoulliPolynomial8 x + 1 / 30) = 0 := by
      nlinarith [hsq]
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      linarith
    · right
      linarith
  rcases hroots with hplus | hminus
  · exfalso
    linarith
  · have hA : 0 ≤ 3 * x ^ 2 * (x - 1) ^ 2 := by positivity
    have hB : 0 ≤ 4 * x * (1 - x) := by positivity
    have hRpos : 0 < 3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2 := by
      nlinarith [hA, hB]
    have hfactor : chapter10BernoulliPolynomial8 x + 1 / 30 =
        x ^ 2 * (1 - x) ^ 2 / 3 *
          (3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2) := by
      rw [chapter10BernoulliPolynomial8]
      ring
    rw [hminus] at hfactor
    have hzero : x ^ 2 * (1 - x) ^ 2 / 3 *
        (3 * x ^ 4 - 6 * x ^ 3 - x ^ 2 + 4 * x + 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp hzero with hleft | hright
    · have hleft' : x ^ 2 * (1 - x) ^ 2 = 0 := by
        nlinarith [hleft]
      rcases mul_eq_zero.mp hleft' with hxpow | h1xpow
      · left
        nlinarith [hxpow]
      · right
        nlinarith [h1xpow]
    · exfalso
      linarith

theorem chapter10_periodic_bernoulli8_abs_le (x : ℝ) :
    |chapter10PeriodicBernoulli8 x| ≤ (1 / 30 : ℝ) := by
  rw [chapter10_periodic_bernoulli8_eq_floor]
  apply chapter10_bernoulli8_abs_le
  rw [Int.self_sub_floor]
  exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

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
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpow := integral_Ioi_rpow_of_lt (a := (-9 : ℝ)) (c := (N : ℝ))
    (by norm_num) hN'
  calc
    (∫ x in Set.Ioi (N : ℝ), 1 / x ^ 9) =
        ∫ x in Set.Ioi (N : ℝ), x ^ (-9 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := lt_trans hN' hx
      rw [Real.rpow_neg hxpos.le]
      norm_num [one_div, Real.rpow_natCast]
    _ = -((N : ℝ) ^ ((-9 : ℝ) + 1)) / ((-9 : ℝ) + 1) := hpow
    _ = 1 / (8 * (N : ℝ) ^ 8) := by
      rw [show ((-9 : ℝ) + 1) = -8 by norm_num]
      have hneg : (N : ℝ) ^ (-8 : ℝ) = ((N : ℝ) ^ 8)⁻¹ := by
        calc
          (N : ℝ) ^ (-8 : ℝ) = ((N : ℝ) ^ (8 : ℝ))⁻¹ :=
            Real.rpow_neg hN'.le 8
          _ = ((N : ℝ) ^ 8)⁻¹ := by norm_num [Real.rpow_natCast]
      rw [hneg]
      field_simp

theorem chapter10_euler_mascheroni_expansion {N : ℕ} (hN : 0 < N) :
    Real.eulerMascheroniConstant =
      chapter10EulerMaclaurinMainTerm N + chapter10EulerMascheroniRemainder N := by
  have hN' : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  unfold chapter10EulerMascheroniRemainder chapter10EulerMaclaurinMainTerm
  field_simp [hN']; ring

private def chapter10EulerDerivative (k : ℕ) : ℝ → ℝ :=
  fun x => (-1 : ℝ) ^ k * (Nat.factorial k : ℝ) * (x ^ (k + 1))⁻¹

private theorem chapter10_euler_derivative_hasDerivAt
    (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (chapter10EulerDerivative k)
      (chapter10EulerDerivative (k + 1) x) x := by
  change HasDerivAt
    (fun y => (-1 : ℝ) ^ k * (Nat.factorial k : ℝ) *
      (y ^ (k + 1))⁻¹)
    (chapter10EulerDerivative (k + 1) x) x
  have h := (hasDerivAt_inv hx).pow (k + 1)
  have h' := h.const_mul ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ))
  have h'' : HasDerivAt
      (fun y => (-1 : ℝ) ^ k * (Nat.factorial k : ℝ) *
        (y ^ (k + 1))⁻¹)
      (-(((-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) *
        ((k + 1 : ℕ) : ℝ) * (x⁻¹) ^ (k + 1 - 1) * (x ^ 2)⁻¹)) x := by
    simpa [chapter10EulerDerivative, mul_assoc] using h'
  rw [show chapter10EulerDerivative (k + 1) x =
      -(((-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) *
        ((k + 1 : ℕ) : ℝ) * (x⁻¹) ^ (k + 1 - 1) * (x ^ 2)⁻¹) by
          dsimp [chapter10EulerDerivative]
          rw [Nat.factorial_succ, inv_pow]
          field_simp [hx]
          push_cast
          ring]
  exact h''

private theorem chapter10_shifted_bernoulli_hasDerivAt
    (n k : ℕ) (hk : 0 < k) {x : ℝ} :
    HasDerivAt
      (fun y : ℝ => chapter10BernoulliPolynomial k (y - (n : ℝ)))
      ((k : ℝ) * chapter10BernoulliPolynomial (k - 1) (x - (n : ℝ))) x := by
  have h := (chapter10_bernoulli_polynomial_derivative hk (x - (n : ℝ))).comp x
    ((hasDerivAt_id x).sub_const (n : ℝ))
  simpa [Function.comp_def] using h

private theorem chapter10_bernoulli_integration_by_parts
    {n k : ℕ} (hn : 0 < n) :
    (∫ x in (n : ℝ)..(n + 1 : ℝ),
      chapter10EulerDerivative k x *
        chapter10BernoulliPolynomial k (x - (n : ℝ))) =
      chapter10EulerDerivative k (n + 1) *
          (chapter10BernoulliPolynomial (k + 1) 1 / ((k + 1 : ℕ) : ℝ)) -
        chapter10EulerDerivative k n *
          (chapter10BernoulliPolynomial (k + 1) 0 / ((k + 1 : ℕ) : ℝ)) -
        (∫ x in (n : ℝ)..(n + 1 : ℝ),
          chapter10EulerDerivative (k + 1) x *
            (chapter10BernoulliPolynomial (k + 1) (x - (n : ℝ)) /
              ((k + 1 : ℕ) : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmem : ∀ x : ℝ, x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ) → 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (n : ℝ) ≤ n + 1)] at hx
    exact lt_of_lt_of_le hnR hx.1
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ),
      HasDerivAt (chapter10EulerDerivative k)
        (chapter10EulerDerivative (k + 1) x) x := by
    intro x hx
    exact chapter10_euler_derivative_hasDerivAt k
      (ne_of_gt (hmem x hx))
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ),
      HasDerivAt
        (fun y : ℝ => chapter10BernoulliPolynomial (k + 1) (y - (n : ℝ)) /
          ((k + 1 : ℕ) : ℝ))
        (chapter10BernoulliPolynomial k (x - (n : ℝ))) x := by
    intro x hx
    have h := (chapter10_shifted_bernoulli_hasDerivAt n (k + 1)
      (Nat.zero_lt_succ k) (x := x)).div_const ((k + 1 : ℕ) : ℝ)
    rw [show k + 1 - 1 = k by omega] at h
    have hK : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcancel : ∀ z : ℝ,
        ((k + 1 : ℕ) : ℝ) * chapter10BernoulliPolynomial k
            (z - (n : ℝ)) / ((k + 1 : ℕ) : ℝ) =
          chapter10BernoulliPolynomial k (z - (n : ℝ)) := by
      intro z
      field_simp
    rw [hcancel x] at h
    exact h
  have hu' : IntervalIntegrable (chapter10EulerDerivative (k + 1))
      volume (n : ℝ) (n + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (chapter10_euler_derivative_hasDerivAt (k + 1)
      (ne_of_gt (hmem x hx))).continuousAt.continuousWithinAt
  have hv' : IntervalIntegrable
      (fun x : ℝ => chapter10BernoulliPolynomial k (x - (n : ℝ)))
      volume (n : ℝ) (n + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    unfold chapter10BernoulliPolynomial
    fun_prop
  simpa [Nat.cast_add, mul_comm] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := chapter10EulerDerivative k)
      (v := fun x : ℝ => chapter10BernoulliPolynomial (k + 1) (x - (n : ℝ)) /
        ((k + 1 : ℕ) : ℝ))
      (u' := chapter10EulerDerivative (k + 1))
      (v' := fun x : ℝ => chapter10BernoulliPolynomial k (x - (n : ℝ)))
      hu hv hu' hv')

private theorem chapter10_bernoulli_endpoint_values :
    chapter10BernoulliPolynomial 1 0 = -(1 / 2 : ℝ) ∧
      chapter10BernoulliPolynomial 1 1 = 1 / 2 ∧
      chapter10BernoulliPolynomial 2 0 = 1 / 6 ∧
      chapter10BernoulliPolynomial 2 1 = 1 / 6 ∧
      chapter10BernoulliPolynomial 3 0 = 0 ∧
      chapter10BernoulliPolynomial 3 1 = 0 ∧
      chapter10BernoulliPolynomial 4 0 = -(1 / 30 : ℝ) ∧
      chapter10BernoulliPolynomial 4 1 = -(1 / 30 : ℝ) ∧
      chapter10BernoulliPolynomial 5 0 = 0 ∧
      chapter10BernoulliPolynomial 5 1 = 0 ∧
      chapter10BernoulliPolynomial 6 0 = 1 / 42 ∧
      chapter10BernoulliPolynomial 6 1 = 1 / 42 ∧
      chapter10BernoulliPolynomial 7 0 = 0 ∧
      chapter10BernoulliPolynomial 7 1 = 0 ∧
      chapter10BernoulliPolynomial 8 0 = -(1 / 30 : ℝ) ∧
      chapter10BernoulliPolynomial 8 1 = -(1 / 30 : ℝ) := by
  have h0 : bernoulli 0 = 1 := by decide +kernel
  have h1 : bernoulli 1 = -1 / 2 := by decide +kernel
  have h2 : bernoulli 2 = 1 / 6 := by decide +kernel
  have h3 : bernoulli 3 = 0 := by decide +kernel
  have h4 : bernoulli 4 = -1 / 30 := by decide +kernel
  have h5 : bernoulli 5 = 0 := by decide +kernel
  have h6 : bernoulli 6 = 1 / 42 := by decide +kernel
  have h7 : bernoulli 7 = 0 := by decide +kernel
  have h8 : bernoulli 8 = -1 / 30 := by decide +kernel
  simp [chapter10BernoulliPolynomial, Finset.sum_range_succ,
    h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num [Nat.choose]

private theorem chapter10_local_euler_maclaurin {n : ℕ} (hn : 0 < n) :
    1 / ((n + 1 : ℕ) : ℝ) =
      (∫ x in (n : ℝ)..(n + 1 : ℝ), chapter10EulerDerivative 0 x) +
        (chapter10EulerDerivative 0 (n + 1) - chapter10EulerDerivative 0 n) / 2 +
        (1 / 12 : ℝ) *
          (chapter10EulerDerivative 1 (n + 1) - chapter10EulerDerivative 1 n) -
        (1 / 720 : ℝ) *
          (chapter10EulerDerivative 3 (n + 1) - chapter10EulerDerivative 3 n) +
        (1 / 30240 : ℝ) *
          (chapter10EulerDerivative 5 (n + 1) - chapter10EulerDerivative 5 n) -
        (1 / 1209600 : ℝ) *
          (chapter10EulerDerivative 7 (n + 1) - chapter10EulerDerivative 7 n) -
        (1 / (Nat.factorial 8 : ℝ)) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10BernoulliPolynomial 8 (x - (n : ℝ)) *
              chapter10EulerDerivative 8 x) := by
  rcases chapter10_bernoulli_endpoint_values with
    ⟨hb10, hb11, hb20, hb21, hb30, hb31, hb40, hb41, hb50, hb51,
      hb60, hb61, hb70, hb71, hb80, hb81⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmem : ∀ x : ℝ, x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ) → 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (n : ℝ) ≤ n + 1)] at hx
    exact lt_of_lt_of_le hnR hx.1
  have hp0 (x : ℝ) :
      chapter10BernoulliPolynomial 0 (x - (n : ℝ)) = 1 := by
    norm_num [chapter10BernoulliPolynomial]
  have hq0 : chapter10EulerDerivative 0 (n + 1) =
      1 / ((n + 1 : ℕ) : ℝ) := by
    simp [chapter10EulerDerivative]
  have hbase :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10BernoulliPolynomial 1 (x - (n : ℝ)) *
          chapter10EulerDerivative 1 x) =
        (chapter10BernoulliPolynomial 1 1) *
            chapter10EulerDerivative 0 (n + 1) -
          (chapter10BernoulliPolynomial 1 0) *
            chapter10EulerDerivative 0 n -
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            (1 : ℝ) * chapter10EulerDerivative 0 x) := by
    have hu : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ),
        HasDerivAt (fun y : ℝ => chapter10BernoulliPolynomial 1 (y - (n : ℝ)))
          1 x := by
      intro x hx
      have h := chapter10_shifted_bernoulli_hasDerivAt n 1 (by norm_num) (x := x)
      rw [show 1 - 1 = 0 by norm_num, hp0 x, mul_one] at h
      norm_num at h
      exact h
    have hv : ∀ x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ),
        HasDerivAt (chapter10EulerDerivative 0)
          (chapter10EulerDerivative 1 x) x := by
      intro x hx
      exact chapter10_euler_derivative_hasDerivAt 0
        (ne_of_gt (hmem x hx))
    have hu' : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
        volume (n : ℝ) (n + 1 : ℝ) :=
      continuousOn_const.intervalIntegrable
    have hv' : IntervalIntegrable (chapter10EulerDerivative 1)
        volume (n : ℝ) (n + 1 : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      exact (chapter10_euler_derivative_hasDerivAt 1
        (ne_of_gt (hmem x hx))).continuousAt.continuousWithinAt
    simpa [Nat.cast_add, hb10, hb11, mul_comm] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := fun x : ℝ => chapter10BernoulliPolynomial 1 (x - (n : ℝ)))
        (v := chapter10EulerDerivative 0)
        (u' := fun _ : ℝ => (1 : ℝ))
        (v' := chapter10EulerDerivative 1)
        hu hv hu' hv')
  have hbase' :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 1 x *
          chapter10BernoulliPolynomial 1 (x - (n : ℝ))) =
        (chapter10EulerDerivative 0 (n + 1) +
          chapter10EulerDerivative 0 n) / 2 -
          (∫ x in (n : ℝ)..(n + 1 : ℝ), chapter10EulerDerivative 0 x) := by
    calc
      _ = (∫ x in (n : ℝ)..(n + 1 : ℝ),
          chapter10BernoulliPolynomial 1 (x - (n : ℝ)) *
            chapter10EulerDerivative 1 x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = chapter10BernoulliPolynomial 1 1 *
            chapter10EulerDerivative 0 (n + 1) -
          chapter10BernoulliPolynomial 1 0 *
            chapter10EulerDerivative 0 n -
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            (1 : ℝ) * chapter10EulerDerivative 0 x) := hbase
      _ = _ := by rw [hb10, hb11]; simp; ring
  have h1 := chapter10_bernoulli_integration_by_parts (n := n) (k := 1) hn
  have h2 := chapter10_bernoulli_integration_by_parts (n := n) (k := 2) hn
  have h3 := chapter10_bernoulli_integration_by_parts (n := n) (k := 3) hn
  have h4 := chapter10_bernoulli_integration_by_parts (n := n) (k := 4) hn
  have h5 := chapter10_bernoulli_integration_by_parts (n := n) (k := 5) hn
  have h6 := chapter10_bernoulli_integration_by_parts (n := n) (k := 6) hn
  have h7 := chapter10_bernoulli_integration_by_parts (n := n) (k := 7) hn
  simp [hb20, hb21, hb30, hb31, hb40, hb41, hb50, hb51,
    hb60, hb61, hb70, hb71, hb80, hb81] at h1 h2 h3 h4 h5 h6 h7
  have hs2 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 2 x *
          (chapter10BernoulliPolynomial 2 (x - (n : ℝ)) / 2)) =
        (1 / 2 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 2 x *
              chapter10BernoulliPolynomial 2 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 2 : ℝ) * (chapter10EulerDerivative 2 x *
            chapter10BernoulliPolynomial 2 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 2 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 2 x *
              chapter10BernoulliPolynomial 2 (x - (n : ℝ))))
  have hs3 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 3 x *
          (chapter10BernoulliPolynomial 3 (x - (n : ℝ)) / 3)) =
        (1 / 3 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 3 x *
              chapter10BernoulliPolynomial 3 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 3 : ℝ) * (chapter10EulerDerivative 3 x *
            chapter10BernoulliPolynomial 3 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 3 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 3 x *
              chapter10BernoulliPolynomial 3 (x - (n : ℝ))))
  have hs4 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 4 x *
          (chapter10BernoulliPolynomial 4 (x - (n : ℝ)) / 4)) =
        (1 / 4 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 4 x *
              chapter10BernoulliPolynomial 4 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 4 : ℝ) * (chapter10EulerDerivative 4 x *
            chapter10BernoulliPolynomial 4 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 4 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 4 x *
              chapter10BernoulliPolynomial 4 (x - (n : ℝ))))
  have hs5 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 5 x *
          (chapter10BernoulliPolynomial 5 (x - (n : ℝ)) / 5)) =
        (1 / 5 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 5 x *
              chapter10BernoulliPolynomial 5 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 5 : ℝ) * (chapter10EulerDerivative 5 x *
            chapter10BernoulliPolynomial 5 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 5 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 5 x *
              chapter10BernoulliPolynomial 5 (x - (n : ℝ))))
  have hs6 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 6 x *
          (chapter10BernoulliPolynomial 6 (x - (n : ℝ)) / 6)) =
        (1 / 6 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 6 x *
              chapter10BernoulliPolynomial 6 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 6 : ℝ) * (chapter10EulerDerivative 6 x *
            chapter10BernoulliPolynomial 6 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 6 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 6 x *
              chapter10BernoulliPolynomial 6 (x - (n : ℝ))))
  have hs7 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 7 x *
          (chapter10BernoulliPolynomial 7 (x - (n : ℝ)) / 7)) =
        (1 / 7 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 7 x *
              chapter10BernoulliPolynomial 7 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 7 : ℝ) * (chapter10EulerDerivative 7 x *
            chapter10BernoulliPolynomial 7 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 7 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 7 x *
              chapter10BernoulliPolynomial 7 (x - (n : ℝ))))
  have hs8 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 8 x *
          (chapter10BernoulliPolynomial 8 (x - (n : ℝ)) / 8)) =
        (1 / 8 : ℝ) *
          (∫ x in (n : ℝ)..(n + 1 : ℝ),
            chapter10EulerDerivative 8 x *
              chapter10BernoulliPolynomial 8 (x - (n : ℝ))) := by
    calc
      _ = ∫ x in (n : ℝ)..(n + 1 : ℝ),
          (1 / 8 : ℝ) * (chapter10EulerDerivative 8 x *
            chapter10BernoulliPolynomial 8 (x - (n : ℝ))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by
        exact
          (intervalIntegral.integral_const_mul
            (a := (n : ℝ)) (b := (n + 1 : ℝ))
            (1 / 8 : ℝ)
            (fun x : ℝ => chapter10EulerDerivative 8 x *
              chapter10BernoulliPolynomial 8 (x - (n : ℝ))))
  rw [hs2] at h1
  rw [hs3] at h2
  rw [hs4] at h3
  rw [hs5] at h4
  rw [hs6] at h5
  rw [hs7] at h6
  rw [hs8] at h7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  have hcomm8 :
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10EulerDerivative 8 x *
          chapter10BernoulliPolynomial 8 (x - (n : ℝ))) =
      (∫ x in (n : ℝ)..(n + 1 : ℝ),
        chapter10BernoulliPolynomial 8 (x - (n : ℝ)) *
          chapter10EulerDerivative 8 x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hcomm8] at h7
  linarith [hq0, hbase', h1, h2, h3, h4, h5, h6, h7]

private theorem chapter10_log_step_bounds {n : ℕ} (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range 21,
        (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
          2 / (n : ℝ) ^ 22 ≤ Real.log (1 + 1 / (n : ℝ)) ∧
      Real.log (1 + 1 / (n : ℝ)) ≤
        (∑ i ∈ Finset.range 21,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
            2 / (n : ℝ) ^ 22 := by
  have hlog :
      |(∑ i ∈ Finset.range 21,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) +
            Real.log (1 - (-(1 / (n : ℝ))))| ≤
        |-(1 / (n : ℝ))| ^ (21 + 1) /
          (1 - |-(1 / (n : ℝ))|) := by
    apply Real.abs_log_sub_add_sum_range_le
    rw [abs_neg, abs_of_pos (by positivity)]
    apply (div_lt_one₀ (by positivity)).2
    exact_mod_cast hn
  norm_num [Finset.sum_range_succ, abs_of_pos, abs_of_nonneg] at hlog ⊢
  have hh := (abs_le.mp hlog).1
  have hh' := (abs_le.mp hlog).2
  have hx : 1 / (n : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hn
  have hd : 0 < 1 - 1 / (n : ℝ) := by linarith
  have hi : 1 / (1 - 1 / (n : ℝ)) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hd).2
    linarith
  have hr :
      (1 / (n : ℝ) ^ 22) / (1 - 1 / (n : ℝ)) ≤
        2 / (n : ℝ) ^ 22 := by
    calc
      (1 / (n : ℝ) ^ 22) / (1 - 1 / (n : ℝ)) =
          (1 / (n : ℝ) ^ 22) * (1 / (1 - 1 / (n : ℝ))) := by ring
      _ ≤ (1 / (n : ℝ) ^ 22) * 2 :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = 2 / (n : ℝ) ^ 22 := by ring
  constructor
  · ring_nf at hr hh ⊢
    linarith
  · ring_nf at hr hh' ⊢
    linarith

private theorem chapter10_q_step_bounds {n : ℕ} (hn : 2 ≤ n) :
    let qL : ℝ → ℝ := fun x =>
      1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) -
        1 / (252 * x ^ 6)
    let qU : ℝ → ℝ := fun x => qL x + 1 / (240 * x ^ 8)
    qL n - qL (n + 1) + 1 / (n + 1 : ℝ) <
          (∑ i ∈ Finset.range 21,
            (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
            2 / (n : ℝ) ^ 22 ∧
      (∑ i ∈ Finset.range 21,
          (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
            2 / (n : ℝ) ^ 22 <
        qU n - qU (n + 1) + 1 / (n + 1 : ℝ) := by
  dsimp
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  let x : ℝ := (n : ℝ) - 2
  have hx : 0 ≤ x := by
    dsimp [x]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnrep : (n : ℝ) = x + 2 := by
    dsimp [x]
    ring
  rw [hnrep]
  norm_num [Finset.sum_range_succ]
  field_simp [ne_of_gt hn0]
  ring_nf
  constructor <;> apply sub_pos.mp <;> ring_nf <;> positivity

private theorem chapter10_harmonic_log_step {n : ℕ} (hn : 0 < n) :
    ((harmonic n : ℝ) - Real.log (n : ℝ)) -
        ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) =
      Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
  have hlog :
      Real.log (n + 1 : ℝ) - Real.log (n : ℝ) =
        Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    ((harmonic n : ℝ) - Real.log (n : ℝ)) -
        ((harmonic (n + 1) : ℝ) - Real.log (n + 1)) =
        Real.log (n + 1 : ℝ) - Real.log (n : ℝ) -
          1 / (n + 1 : ℝ) := by
      rw [harmonic_succ]
      norm_num
      ring
    _ = Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
      rw [hlog]

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
  by_cases hN1 : N = 1
  · subst N
    have hg0 :=
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.chapter09_gamma_directed_bounds
    have hg :
        (577215664901532 / 10 ^ 15 : ℝ) < Real.eulerMascheroniConstant ∧
          Real.eulerMascheroniConstant < (577215664901533 / 10 ^ 15 : ℝ) := by
      simpa [LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.chapter09GammaLower,
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.chapter09GammaUpper,
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.chapter09EulerMascheroni]
        using hg0
    rw [abs_lt]
    unfold chapter10EulerMascheroniRemainder chapter10EulerMaclaurinMainTerm
      chapter10Harmonic
    norm_num [harmonic, Finset.sum_range_succ]
    constructor <;> linarith [hg.1, hg.2]
  have hN2 : 2 ≤ N := by omega
  let qL : ℝ → ℝ := fun x =>
    1 / (2 * x) - 1 / (12 * x ^ 2) + 1 / (120 * x ^ 4) -
      1 / (252 * x ^ 6)
  let r : ℝ → ℝ := fun x => 1 / (240 * x ^ 8)
  let a : ℕ → ℝ := fun n =>
    (harmonic n : ℝ) - Real.log (n : ℝ)
  let F : ℕ → ℝ := fun n => a n - qL n
  let H : ℕ → ℝ := fun n => F n - r n
  have hqLlim : Tendsto (fun n : ℕ => qL n) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop
        (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hterm (c : ℝ) (k : ℕ) (hk : 0 < k) :
        Tendsto (fun n : ℕ => c * (1 / (n : ℝ)) ^ k) atTop (nhds 0) := by
      simpa [zero_pow (Nat.ne_of_gt hk)] using
        (tendsto_const_nhds.mul (hinv.pow k) :
          Tendsto (fun n : ℕ => c * (1 / (n : ℝ)) ^ k)
            atTop (nhds (c * 0 ^ k)))
    have h := (((hterm (1 / 2) 1 (by norm_num)).sub
      (hterm (1 / 12) 2 (by norm_num))).add
      (hterm (1 / 120) 4 (by norm_num))).sub
      (hterm (1 / 252) 6 (by norm_num))
    convert h using 1
    · funext n
      dsimp [qL]
      ring
    · norm_num
  have hrlim : Tendsto (fun n : ℕ => r n) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop
        (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h :=
      (tendsto_const_nhds.mul (hinv.pow 8) :
        Tendsto (fun n : ℕ => (1 / 240 : ℝ) *
          (1 / (n : ℝ)) ^ 8) atTop (nhds ((1 / 240 : ℝ) * 0 ^ 8)))
    convert h using 1
    · funext n
      dsimp [r]
      field_simp
    · norm_num
  have hFlim : Tendsto F atTop (nhds Real.eulerMascheroniConstant) := by
    have ha : Tendsto a atTop (nhds Real.eulerMascheroniConstant) := by
      simpa [a] using Real.tendsto_harmonic_sub_log
    simpa [F] using ha.sub hqLlim
  have hHlim : Tendsto H atTop (nhds Real.eulerMascheroniConstant) := by
    simpa [H] using hFlim.sub hrlim
  have hFstep (n : ℕ) (hn : 2 ≤ n) : F (n + 1) < F n := by
    have hs := chapter10_harmonic_log_step (n := n) (by omega)
    have hlog := chapter10_log_step_bounds (n := n) hn
    have hq :
        qL (n : ℝ) - qL (n + 1) + 1 / (n + 1 : ℝ) <
            (∑ i ∈ Finset.range 21,
              (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
              2 / (n : ℝ) ^ 22 ∧
          (∑ i ∈ Finset.range 21,
              (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
              2 / (n : ℝ) ^ 22 <
            (qL (n : ℝ) + r (n : ℝ)) -
              (qL (n + 1) + r (n + 1)) + 1 / (n + 1 : ℝ) := by
      simpa [qL, r] using (chapter10_q_step_bounds (n := n) hn)
    dsimp [F, a] at ⊢
    norm_num [Nat.cast_add, Nat.cast_one, one_div] at hs hlog hq ⊢
    linarith [hs, hlog.1, hq.1]
  have hFdiff (n : ℕ) (hn : 2 ≤ n) :
      F n - F (n + 1) < r n - r (n + 1) := by
    have hs := chapter10_harmonic_log_step (n := n) (by omega)
    have hlog := chapter10_log_step_bounds (n := n) hn
    have hq :
        qL (n : ℝ) - qL (n + 1) + 1 / (n + 1 : ℝ) <
            (∑ i ∈ Finset.range 21,
              (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) -
              2 / (n : ℝ) ^ 22 ∧
          (∑ i ∈ Finset.range 21,
              (-(1 / (n : ℝ))) ^ (i + 1) / (i + 1 : ℝ)) * (-1) +
              2 / (n : ℝ) ^ 22 <
            (qL (n : ℝ) + r (n : ℝ)) -
              (qL (n + 1) + r (n + 1)) + 1 / (n + 1 : ℝ) := by
      simpa [qL, r] using (chapter10_q_step_bounds (n := n) hn)
    dsimp [F, a] at ⊢
    norm_num [Nat.cast_add, Nat.cast_one, one_div] at hs hlog hq ⊢
    linarith [hs, hlog.2, hq.2]
  have hHstep (n : ℕ) (hn : 2 ≤ n) : H n < H (n + 1) := by
    have h := hFdiff n hn
    dsimp [H] at ⊢
    norm_num [Nat.cast_add, Nat.cast_one] at h ⊢
    linarith
  have hFbound (m : ℕ) (hm : N + 1 ≤ m) : F m ≤ F (N + 1) := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
        exact (hFstep m (by omega)).le.trans ih
  have hHbound (m : ℕ) (hm : N + 1 ≤ m) : H (N + 1) ≤ H m := by
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | @succ m hm ih =>
        exact ih.trans (hHstep m (by omega)).le
  have hgamma_le : Real.eulerMascheroniConstant ≤ F (N + 1) := by
    apply le_of_tendsto hFlim
    exact eventually_atTop.2 ⟨N + 1, fun m hm => hFbound m hm⟩
  have hH_le : H (N + 1) ≤ Real.eulerMascheroniConstant := by
    apply ge_of_tendsto hHlim
    exact eventually_atTop.2 ⟨N + 1, fun m hm => hHbound m hm⟩
  have hgamma_lt : Real.eulerMascheroniConstant < F N := by
    exact lt_of_le_of_lt hgamma_le (hFstep N hN2)
  have hH_lt : H N < Real.eulerMascheroniConstant := by
    exact lt_of_lt_of_le (hHstep N hN2) hH_le
  have hrem_bound : F N - Real.eulerMascheroniConstant < r N := by
    dsimp [H] at hH_lt
    linarith
  have hmain : chapter10EulerMaclaurinMainTerm N = F N := by
    dsimp [F, a, qL]
    unfold chapter10EulerMaclaurinMainTerm chapter10Harmonic
    ring
  have hrem : chapter10EulerMascheroniRemainder N =
      Real.eulerMascheroniConstant - F N := by
    unfold chapter10EulerMascheroniRemainder
    rw [hmain]
  rw [hrem, abs_of_neg (by linarith)]
  have hrN : r N = 1 / (240 * (N : ℝ) ^ 8) := by
    rfl
  have hneg : -(Real.eulerMascheroniConstant - F N) < r N := by
    linarith [hrem_bound]
  simpa [hrN] using hneg

/- The decimals in (10.4) are represented by named rational endpoints so that later ledgers can
   reuse them as exact data rather than as floating-point notation. -/
def chapter10GammaLower : ℚ := 577215664901532 / 10 ^ 15

def chapter10GammaUpper : ℚ := 577215664901533 / 10 ^ 15

def chapter10PiLower : ℚ := 3141592653589793 / 10 ^ 15

def chapter10PiUpper : ℚ := 3141592653589794 / 10 ^ 15

theorem chapter10_gamma_directed_bounds :
    (chapter10GammaLower : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (chapter10GammaUpper : ℝ) := by
  exact LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.chapter09_gamma_directed_bounds

theorem chapter10_pi_directed_bounds :
    (chapter10PiLower : ℝ) < Real.pi ∧
      Real.pi < (chapter10PiUpper : ℝ) := by
  have ha := chapter10_arctan_alternating_remainder_bound
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 12
  have hb := chapter10_arctan_alternating_remainder_bound
    (x := (1 / 239 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [chapter10ArctanRemainder, chapter10ArctanPartialSum,
    chapter10ArctanNextTerm, Finset.sum_range_succ] at ha hb
  rw [chapter10_machin_formula]
  norm_num [chapter10PiLower, chapter10PiUpper]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
