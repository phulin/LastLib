import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section02TheThresholdThreeSqrtThree
import Mathlib.Analysis.Real.Pi.Bounds

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
open Filter
open scoped Topology

private theorem chapter11_two_prime_log_two_bounds :
    (0.6931471805599453093 : ℝ) < Real.log 2 ∧
      Real.log 2 < (0.69314718055994531 : ℝ) := by
  have hid := Chapter10.chapter10_log_two_series_identity 18
  have hrem := Chapter10.chapter10_log_two_series_remainder_bound 18
  have hupper :
      Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 18 ≤
        2 * |(1 / 3 : ℝ)| ^ (2 * 18 + 3) /
          (((2 * 18 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) :=
    (le_abs_self _).trans hrem
  have hlower :
      -(2 * |(1 / 3 : ℝ)| ^ (2 * 18 + 3) /
          (((2 * 18 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 18 := by
    have hneg := neg_le_abs (Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 18)
    linarith
  constructor
  · rw [hid]
    calc
      (0.6931471805599453093 : ℝ) <
          Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 18 -
            2 * |(1 / 3 : ℝ)| ^ (2 * 18 + 3) /
              (((2 * 18 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 18 +
          Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 18 := by
        linarith
  · rw [hid]
    calc
      Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 18 +
          Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 18 ≤
          Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 18 +
            2 * |(1 / 3 : ℝ)| ^ (2 * 18 + 3) /
              (((2 * 18 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) :=
        add_le_add_right hupper _
      _ < (0.69314718055994531 : ℝ) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]

private theorem chapter11_two_prime_log_five_fourths_bounds :
    (0.2231435513142097 : ℝ) < Real.log (5 / 4 : ℝ) ∧
      Real.log (5 / 4 : ℝ) < (0.22314355131420976 : ℝ) := by
  have hid := Chapter10.chapter10_log_series_identity (1 / 9 : ℝ) 10
  have harg :
      (1 + (1 / 9 : ℝ)) / (1 - (1 / 9 : ℝ)) = (5 / 4 : ℝ) := by
    norm_num
  have hid' :
      Real.log (5 / 4 : ℝ) =
        Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 10 +
          Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10 := by
    rw [← harg]
    exact hid
  have hrem := Chapter10.chapter10_log_series_remainder_bound
    (y := (1 / 9 : ℝ)) (by norm_num) 10
  have hupper :
      Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10 ≤
        2 * |(1 / 9 : ℝ)| ^ (2 * 10 + 3) /
          (((2 * 10 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2)) :=
    (le_abs_self _).trans hrem
  have hlower :
      -(2 * |(1 / 9 : ℝ)| ^ (2 * 10 + 3) /
          (((2 * 10 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10 := by
    have hneg := neg_le_abs (Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10)
    linarith
  constructor
  · rw [hid']
    calc
      (0.2231435513142097 : ℝ) <
          Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 10 -
            2 * |(1 / 9 : ℝ)| ^ (2 * 10 + 3) /
              (((2 * 10 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 10 +
          Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10 := by
        linarith
  · rw [hid']
    calc
      Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 10 +
          Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 10 ≤
          Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 10 +
            2 * |(1 / 9 : ℝ)| ^ (2 * 10 + 3) /
              (((2 * 10 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2)) :=
        add_le_add_right hupper _
      _ < (0.22314355131420976 : ℝ) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]

private theorem chapter11_two_prime_log_three_halves_bounds :
    (0.4054651081081643819 : ℝ) < Real.log (3 / 2 : ℝ) ∧
      Real.log (3 / 2 : ℝ) < (0.4054651081081644 : ℝ) := by
  have hid := Chapter10.chapter10_log_series_identity (1 / 5 : ℝ) 12
  have harg :
      (1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ)) = (3 / 2 : ℝ) := by
    norm_num
  have hid' :
      Real.log (3 / 2 : ℝ) =
        Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 12 +
          Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12 := by
    rw [← harg]
    exact hid
  have hrem := Chapter10.chapter10_log_series_remainder_bound
    (y := (1 / 5 : ℝ)) (by norm_num) 12
  have hupper :
      Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12 ≤
        2 * |(1 / 5 : ℝ)| ^ (2 * 12 + 3) /
          (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) :=
    (le_abs_self _).trans hrem
  have hlower :
      -(2 * |(1 / 5 : ℝ)| ^ (2 * 12 + 3) /
          (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12 := by
    have hneg := neg_le_abs (Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12)
    linarith
  constructor
  · rw [hid']
    calc
      (0.4054651081081643819 : ℝ) <
          Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 12 -
            2 * |(1 / 5 : ℝ)| ^ (2 * 12 + 3) /
              (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 12 +
          Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12 := by
        linarith
  · rw [hid']
    calc
      Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 12 +
          Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 12 ≤
          Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 12 +
            2 * |(1 / 5 : ℝ)| ^ (2 * 12 + 3) /
              (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) :=
        add_le_add_right hupper _
      _ < (0.4054651081081644 : ℝ) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]

private theorem chapter11_two_prime_gamma_lower :
    (0.5772156649015325 : ℝ) < Real.eulerMascheroniConstant := by
  have hlog2 := chapter11_two_prime_log_two_bounds.2
  have hlog54 := chapter11_two_prime_log_five_fourths_bounds.2
  have hlog100eq :
      Real.log (100 : ℝ) = 6 * Real.log 2 + 2 * Real.log (5 / 4 : ℝ) := by
    calc
      Real.log (100 : ℝ) =
          Real.log ((2 : ℝ) ^ (6 : ℕ) * (5 / 4 : ℝ) ^ (2 : ℕ)) := by
        norm_num
      _ = Real.log ((2 : ℝ) ^ (6 : ℕ)) +
          Real.log ((5 / 4 : ℝ) ^ (2 : ℕ)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 6 * Real.log 2 + 2 * Real.log (5 / 4 : ℝ) := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  have hlog100 : Real.log (100 : ℝ) <
      6 * (0.69314718055994531 : ℝ) +
        2 * (0.22314355131420976 : ℝ) := by
    rw [hlog100eq]
    exact add_lt_add
      (mul_lt_mul_of_pos_left hlog2 (by norm_num))
      (mul_lt_mul_of_pos_left hlog54 (by norm_num))
  have hexpansion := Chapter10.chapter10_euler_mascheroni_expansion
    (N := 100) (by norm_num)
  have hrem := Chapter10.chapter10_euler_mascheroni_remainder_bound
    (N := 100) (by norm_num)
  have hrem_lower :
      -(1 / (240 * (100 : ℝ) ^ 8)) <
        Chapter10.chapter10EulerMascheroniRemainder 100 := by
    have hneg := neg_le_abs (Chapter10.chapter10EulerMascheroniRemainder 100)
    linarith
  rw [hexpansion]
  unfold Chapter10.chapter10EulerMaclaurinMainTerm
  norm_num [Chapter10.chapter10Harmonic, harmonic, Finset.sum_range_succ]
  nlinarith [hlog100, hrem_lower]

private theorem chapter11_two_prime_log_pi_third_lower :
    (0.0461175971812904827 : ℝ) <
      Real.log (104719755119659774615 / 100000000000000000000 : ℝ) := by
  have hid := Chapter10.chapter10_log_series_identity
    (943951023931954923 / 40943951023931954923 : ℝ) 5
  have harg :
      (1 + (943951023931954923 / 40943951023931954923 : ℝ)) /
          (1 - (943951023931954923 / 40943951023931954923 : ℝ)) =
        (104719755119659774615 / 100000000000000000000 : ℝ) := by
    norm_num
  have hid' :
      Real.log (104719755119659774615 / 100000000000000000000 : ℝ) =
        Chapter10.chapter10LogPartialSum
            (943951023931954923 / 40943951023931954923 : ℝ) 5 +
          Chapter10.chapter10LogRemainder
            (943951023931954923 / 40943951023931954923 : ℝ) 5 := by
    rw [← harg]
    exact hid
  have hrem := Chapter10.chapter10_log_series_remainder_bound
    (y := (943951023931954923 / 40943951023931954923 : ℝ)) (by norm_num) 5
  have hlower :
      -(2 * |(943951023931954923 / 40943951023931954923 : ℝ)| ^ (2 * 5 + 3) /
          (((2 * 5 + 3 : ℕ) : ℝ) *
            (1 - (943951023931954923 / 40943951023931954923 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder
            (943951023931954923 / 40943951023931954923 : ℝ) 5 := by
    have hneg := neg_le_abs
      (Chapter10.chapter10LogRemainder
        (943951023931954923 / 40943951023931954923 : ℝ) 5)
    linarith
  rw [hid']
  calc
    (0.0461175971812904827 : ℝ) <
        Chapter10.chapter10LogPartialSum
            (943951023931954923 / 40943951023931954923 : ℝ) 5 -
          2 * |(943951023931954923 / 40943951023931954923 : ℝ)| ^ (2 * 5 + 3) /
            (((2 * 5 + 3 : ℕ) : ℝ) *
              (1 - (943951023931954923 / 40943951023931954923 : ℝ) ^ 2)) := by
      norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
    _ ≤ Chapter10.chapter10LogPartialSum
          (943951023931954923 / 40943951023931954923 : ℝ) 5 +
        Chapter10.chapter10LogRemainder
          (943951023931954923 / 40943951023931954923 : ℝ) 5 := by
      linarith

/-! ## 11.4. The two-prime threshold `3^(3/2) 2^(2/3)` -/

def chapter11TwoPrimeCeiling : ℝ :=
  Real.rpow 3 (3 / 2 : ℝ) * Real.rpow 2 (2 / 3 : ℝ)

theorem chapter11_two_prime_ceiling_decimal_enclosure :
    (8.248377821991615 : ℝ) < chapter11TwoPrimeCeiling ∧
      chapter11TwoPrimeCeiling < 8.248377821991617 := by
  have hpow : chapter11TwoPrimeCeiling ^ (6 : ℕ) = (314928 : ℝ) := by
    unfold chapter11TwoPrimeCeiling
    have h3pow :
        (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) ^ (6 : ℕ) =
          Real.rpow (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) (6 : ℝ) :=
      (Real.rpow_natCast (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) 6).symm
    have h2pow :
        (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) ^ (6 : ℕ) =
          Real.rpow (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) (6 : ℝ) :=
      (Real.rpow_natCast (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) 6).symm
    calc
      (Real.rpow (3 : ℝ) (3 / 2 : ℝ) *
          Real.rpow (2 : ℝ) (2 / 3 : ℝ)) ^ (6 : ℕ) =
          (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) ^ (6 : ℕ) *
            (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) ^ (6 : ℕ) := by
        rw [mul_pow]
      _ = Real.rpow (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) (6 : ℝ) *
          Real.rpow (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) (6 : ℝ) := by
        rw [h3pow, h2pow]
      _ = Real.rpow (3 : ℝ) ((3 / 2 : ℝ) * (6 : ℝ)) *
          Real.rpow (2 : ℝ) ((2 / 3 : ℝ) * (6 : ℝ)) := by
        have h3mul :
            Real.rpow (Real.rpow (3 : ℝ) (3 / 2 : ℝ)) (6 : ℝ) =
              Real.rpow (3 : ℝ) ((3 / 2 : ℝ) * (6 : ℝ)) :=
          (Real.rpow_mul (by norm_num) (3 / 2 : ℝ) (6 : ℝ)).symm
        have h2mul :
            Real.rpow (Real.rpow (2 : ℝ) (2 / 3 : ℝ)) (6 : ℝ) =
              Real.rpow (2 : ℝ) ((2 / 3 : ℝ) * (6 : ℝ)) :=
          (Real.rpow_mul (by norm_num) (2 / 3 : ℝ) (6 : ℝ)).symm
        rw [h3mul, h2mul]
      _ = (314928 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hnonneg : 0 ≤ chapter11TwoPrimeCeiling := by
    unfold chapter11TwoPrimeCeiling
    exact mul_nonneg
      (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.rpow_pos_of_pos (by norm_num) _).le
  constructor
  · apply lt_of_pow_lt_pow_left₀ 6 hnonneg
    rw [hpow]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 6 (by norm_num)
    rw [hpow]
    norm_num

theorem chapter11_two_prime_ceiling_log_eq :
    Real.log chapter11TwoPrimeCeiling =
      (3 / 2 : ℝ) * Real.log 3 + (2 / 3 : ℝ) * Real.log 2 := by
  unfold chapter11TwoPrimeCeiling
  have h3 : Real.rpow (3 : ℝ) (3 / 2 : ℝ) =
      Real.exp (Real.log (3 : ℝ) * (3 / 2 : ℝ)) :=
    Real.rpow_def_of_pos (x := (3 : ℝ)) (y := (3 / 2 : ℝ)) (by norm_num)
  have h2 : Real.rpow (2 : ℝ) (2 / 3 : ℝ) =
      Real.exp (Real.log (2 : ℝ) * (2 / 3 : ℝ)) :=
    Real.rpow_def_of_pos (x := (2 : ℝ)) (y := (2 / 3 : ℝ)) (by norm_num)
  rw [h3, h2, Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_exp]
  ring

theorem chapter11_two_prime_ceiling_log_upper :
    Real.log chapter11TwoPrimeCeiling < 2.110016553375462 := by
  have hlog2 := chapter11_two_prime_log_two_bounds.2
  have hlog54 := chapter11_two_prime_log_three_halves_bounds.2
  have hlog3eq : Real.log (3 : ℝ) =
      Real.log 2 + Real.log (3 / 2 : ℝ) := by
    calc
      Real.log (3 : ℝ) = Real.log ((2 : ℝ) * (3 / 2 : ℝ)) := by
        norm_num
      _ = Real.log 2 + Real.log (3 / 2 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  have hlog3 : Real.log (3 : ℝ) <
      (0.69314718055994531 : ℝ) + 0.4054651081081644 := by
    rw [hlog3eq]
    linarith
  calc
    Real.log chapter11TwoPrimeCeiling =
        (3 / 2 : ℝ) * Real.log 3 + (2 / 3 : ℝ) * Real.log 2 :=
      chapter11_two_prime_ceiling_log_eq
    _ < (3 / 2 : ℝ) *
          ((0.69314718055994531 : ℝ) + 0.4054651081081644) +
        (2 / 3 : ℝ) * (0.69314718055994531 : ℝ) := by
      exact add_lt_add
        (mul_lt_mul_of_pos_left hlog3 (by norm_num))
        (mul_lt_mul_of_pos_left hlog2 (by norm_num))
    _ < (2.110016553375462 : ℝ) := by
      norm_num

def chapter11TwoPrimeLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (12 : ℝ) / 21 - 1.10356

theorem chapter11_two_prime_log_endpoint_lower :
    (2.126398521002197 : ℝ) < chapter11TwoPrimeLogEndpoint := by
  have hlog2 := chapter11_two_prime_log_two_bounds.1
  have hlog15 := chapter11_two_prime_log_three_halves_bounds.1
  have hlogq := chapter11_two_prime_log_pi_third_lower
  have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hqpi :
      (104719755119659774615 / 100000000000000000000 : ℝ) < Real.pi / 3 := by
    nlinarith [hpi]
  have hA :
      (16 : ℝ) * (3 / 2 : ℝ) *
          (104719755119659774615 / 100000000000000000000 : ℝ) <
        8 * Real.pi := by
    nlinarith [hqpi]
  have hlogA :
      Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
          (104719755119659774615 / 100000000000000000000 : ℝ)) =
        4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (104719755119659774615 / 100000000000000000000 : ℝ) := by
    calc
      Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
          (104719755119659774615 / 100000000000000000000 : ℝ)) =
          Real.log ((16 : ℝ) * (3 / 2 : ℝ)) +
            Real.log (104719755119659774615 / 100000000000000000000 : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (16 : ℝ) + Real.log (3 / 2 : ℝ) +
            Real.log (104719755119659774615 / 100000000000000000000 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
            Real.log (104719755119659774615 / 100000000000000000000 : ℝ) := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
  have hlogprod :
      4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (104719755119659774615 / 100000000000000000000 : ℝ) <
        Real.log (8 * Real.pi) := by
    calc
      4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (104719755119659774615 / 100000000000000000000 : ℝ) =
          Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
            (104719755119659774615 / 100000000000000000000 : ℝ)) := hlogA.symm
      _ < Real.log (8 * Real.pi) := by
        exact Real.strictMonoOn_log
          (Set.mem_Ioi.mpr (by positivity))
          (Set.mem_Ioi.mpr (by positivity)) hA
  have hγ := chapter11_two_prime_gamma_lower
  unfold chapter11TwoPrimeLogEndpoint
  nlinarith

theorem chapter11_two_prime_log_margin :
    (0.016381967626735 : ℝ) <
      chapter11TwoPrimeLogEndpoint - 2.110016553375462 := by
  have h := chapter11_two_prime_log_endpoint_lower
  nlinarith

theorem chapter11_two_prime_degree_twenty_one_log_expression_lower :
    (2.126398521002197 : ℝ) <
      chapter11ExplicitFormulaLogExpression 21 6 0 := by
  have hrow := Chapter10.chapter10_archimedean_ledger_row_six
  have hB : chapter11B 6 ≤ (1.10356 : ℝ) := by
    rw [chapter11_B_eq_chapter10_BT]
    have hb := hrow.2.2.1
    have hb' : Chapter10.chapter10BT 6 < (1.10356 : ℝ) := by
      convert hb using 1
      norm_num [Chapter10.chapter10RowSix]
    exact hb'.le
  have hbase := chapter11_explicit_formula_log_expression_ge_of_B_upper
    21 6 0 (1.10356 : ℝ) hB
  calc
    (2.126398521002197 : ℝ) < chapter11TwoPrimeLogEndpoint :=
      chapter11_two_prime_log_endpoint_lower
    _ ≤ chapter11ExplicitFormulaLogExpression 21 6 0 := by
      unfold chapter11TwoPrimeLogEndpoint
      convert hbase using 1; norm_num

theorem chapter11_two_prime_degree_twenty_one_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 21 ≤ chapter11Degree K) :
    (2.126398521002197 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  have hbase := chapter11_two_prime_degree_twenty_one_log_expression_lower
  have hdegree_mono := chapter11_explicit_formula_log_expression_mono_degree
    (hm := by norm_num) hdegree 6 (by norm_num) 0
  have hC : chapter11C 6 ≤ Real.pi / 2 := by
    rw [chapter11_C_eq_chapter10_CT, Chapter10.chapter10_CT_eq_chapter09_CT]
    exact (Chapter09.chapter09_unconditional_archimedean_C_lt_pi_div_two
      (by norm_num)).le
  have hα := chapter11_real_proportion_nonneg K
  have hsignature := chapter11_explicit_formula_log_expression_mono_signature
    (chapter11Degree K) 6 0 (chapter11RealProportion K) hα hC
  have hbound := chapter11_explicit_formula_log_root_discriminant_bound
    K 6 (by norm_num)
  calc
    (2.126398521002197 : ℝ) <
        chapter11ExplicitFormulaLogExpression 21 6 0 := hbase
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K) 6 0 :=
      hdegree_mono
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K) 6
        (chapter11RealProportion K) := hsignature
    _ ≤ Real.log (chapter11RootDiscriminant K) := hbound

theorem chapter11_two_prime_degree_twenty_one_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 21 ≤ chapter11Degree K) :
    (8.38461535304387 : ℝ) < chapter11RootDiscriminant K := by
  have hexplower : (8.38461535304387 : ℝ) <
      Real.exp (2.126398521002197 : ℝ) := by
    calc
      (8.38461535304387 : ℝ) <
          ∑ k ∈ Finset.range 24,
            (2.126398521002197 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp (2.126398521002197 : ℝ) := by
        simpa using (Real.sum_le_exp_of_nonneg
          (x := (2.126398521002197 : ℝ)) (by norm_num) 24)
  have hlog := chapter11_two_prime_degree_twenty_one_log_lower K hdegree
  calc
    (8.38461535304387 : ℝ) <
        Real.exp (2.126398521002197 : ℝ) := hexplower
    _ < Real.exp (Real.log (chapter11RootDiscriminant K)) :=
      Real.exp_lt_exp.mpr hlog
    _ = chapter11RootDiscriminant K :=
      Real.exp_log (chapter11_root_discriminant_pos K)

theorem chapter11_two_prime_ceiling_below_degree_twenty_one_root_endpoint :
    chapter11TwoPrimeCeiling < 8.38461535304387 := by
  exact (chapter11_two_prime_ceiling_decimal_enclosure.2).trans
    (by norm_num : (8.248377821991617 : ℝ) < 8.38461535304387)

theorem chapter11_two_prime_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11TwoPrimeCeiling) :
    chapter11Degree K ≤ 20 := by
  by_contra hnot
  have hdegree : 21 ≤ chapter11Degree K := by omega
  have hroot := chapter11_two_prime_degree_twenty_one_root_lower K hdegree
  have hupper : chapter11RootDiscriminant K < 8.38461535304387 :=
    hceiling.trans chapter11_two_prime_ceiling_below_degree_twenty_one_root_endpoint
  exact (lt_irrefl (8.38461535304387 : ℝ)) (hroot.trans hupper)

theorem chapter11_two_prime_ceiling_does_not_cross_degree_fifty_three_minkowski :
    ¬ chapter11TwoPrimeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  have hev : ∀ᶠ m : ℕ in atTop,
      chapter02FactorialFactor 53 ≤ chapter02FactorialFactor m := by
    filter_upwards [eventually_ge_atTop 53] with m hm
    have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
    exact chapter02_factorial_factor_monotone (by norm_num)
      (by simpa using hmpos) hm
  have hfactor02 : chapter02FactorialFactor 53 ≤ Real.exp 2 :=
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => chapter02FactorialFactor 53) atTop
          (𝓝 (chapter02FactorialFactor 53)))
      chapter02_factorial_factor_tendsto hev
  have hfactor : chapter11MinkowskiFactor 53 ≤ Real.exp 2 := by
    rw [chapter11_minkowski_factor_of_pos 53 (by norm_num)]
    simpa [chapter02FactorialFactor] using hfactor02
  have hfactor_nonneg : 0 ≤ chapter11MinkowskiFactor 53 := by
    rw [chapter11_minkowski_factor_of_pos 53 (by norm_num)]
    exact (Real.rpow_pos_of_pos (div_pos (by positivity) (by positivity)) _).le
  have hpi : Real.pi / 4 ≤ (1 : ℝ) := by
    linarith [Real.pi_lt_four]
  have hprod :
      (Real.pi / 4) * chapter11MinkowskiFactor 53 ≤
      chapter11MinkowskiFactor 53 :=
    by simpa using mul_le_mul_of_nonneg_right hpi hfactor_nonneg
  have hprod' :
      (Real.pi / 4) * chapter11MinkowskiFactor 53 ≤ Real.exp 2 :=
    hprod.trans hfactor
  have hfivepow : chapter02FiveToFiveFourth ^ (4 : ℕ) = (3125 : ℝ) := by
    unfold chapter02FiveToFiveFourth
    calc
      (Real.rpow (5 : ℝ) ((5 : ℝ) / 4)) ^ (4 : ℕ) =
          Real.rpow (Real.rpow (5 : ℝ) ((5 : ℝ) / 4)) (4 : ℝ) := by
        exact (Real.rpow_natCast
          (Real.rpow (5 : ℝ) ((5 : ℝ) / 4)) 4).symm
      _ = Real.rpow (5 : ℝ) (((5 : ℝ) / 4) * (4 : ℝ)) :=
        (Real.rpow_mul (by norm_num) ((5 : ℝ) / 4) (4 : ℝ)).symm
      _ = (3125 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hfive : chapter02FiveToFiveFourth < (8 : ℝ) := by
    have hnonneg : 0 ≤ chapter02FiveToFiveFourth := by
      unfold chapter02FiveToFiveFourth
      exact (Real.rpow_pos_of_pos (by norm_num) _).le
    apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 8)
    rw [hfivepow]
    norm_num
  have hU : (8 : ℝ) < chapter11TwoPrimeCeiling :=
    (by norm_num : (8 : ℝ) < 8.248377821991615).trans
      chapter11_two_prime_ceiling_decimal_enclosure.1
  have hproduct_lt :
      (Real.pi / 4) * chapter11MinkowskiFactor 53 < chapter11TwoPrimeCeiling :=
    have hexpU : Real.exp 2 < chapter11TwoPrimeCeiling :=
      chapter02_totally_real_limit_below_five_to_five_fourth.trans
        (hfive.trans hU)
    hprod'.trans_lt hexpU
  intro hcross
  exact (lt_irrefl (chapter11TwoPrimeCeiling)) (hcross.trans hproduct_lt)

theorem chapter11_three_sqrt_three_lt_two_prime_ceiling :
    chapter11ThreeSqrtThreeCeiling < chapter11TwoPrimeCeiling := by
  exact (chapter11_three_sqrt_three_ceiling_enclosure.2.trans
      (by norm_num : (5.1961524228 : ℝ) < 8.248377821991615)).trans
    chapter11_two_prime_ceiling_decimal_enclosure.1

/- (11.8a) is a separate certificate: it reuses the degree-21 crossing at the
   larger ceiling, so it does not erase the independent degree-53 geometric
   certificate from §11.2. -/
theorem chapter11_three_sqrt_three_explicit_formula_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 20 := by
  exact chapter11_two_prime_degree_cutoff K
    (hceiling.trans chapter11_three_sqrt_three_lt_two_prime_ceiling)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
