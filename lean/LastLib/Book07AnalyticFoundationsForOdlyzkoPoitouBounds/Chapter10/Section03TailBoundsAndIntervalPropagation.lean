import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.Section02FiniteFormulasForBTAndCT

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## 10.3. Tail bounds and interval propagation -/

def chapter10IntervalAdd
    (I J : Chapter10RationalInterval) : Chapter10RationalInterval :=
  { lower := I.lower + J.lower
    upper := I.upper + J.upper }

def chapter10IntervalSub
    (I J : Chapter10RationalInterval) : Chapter10RationalInterval :=
  { lower := I.lower - J.upper
    upper := I.upper - J.lower }

def chapter10IntervalScaleNonnegative
    (q : ℚ) (I : Chapter10RationalInterval) : Chapter10RationalInterval :=
  { lower := q * I.lower
    upper := q * I.upper }

def chapter10IntervalMulNonnegative
    (I J : Chapter10RationalInterval) : Chapter10RationalInterval :=
  { lower := I.lower * J.lower
    upper := I.upper * J.upper }

theorem chapter10_interval_add_valid
    {I J : Chapter10RationalInterval} (hI : I.Valid) (hJ : J.Valid) :
    (chapter10IntervalAdd I J).Valid := by
  sorry

theorem chapter10_interval_sub_valid
    {I J : Chapter10RationalInterval} (hI : I.Valid) (hJ : J.Valid) :
    (chapter10IntervalSub I J).Valid := by
  sorry

theorem chapter10_interval_scale_nonnegative_valid
    {q : ℚ} {I : Chapter10RationalInterval}
    (hq : 0 ≤ q) (hI : I.Valid) :
    (chapter10IntervalScaleNonnegative q I).Valid := by
  sorry

theorem chapter10_interval_scale_nonnegative_contains
    {q : ℚ} {I : Chapter10RationalInterval} {x : ℝ}
    (hq : 0 ≤ q) (hx : I.Contains x) :
    (chapter10IntervalScaleNonnegative q I).Contains ((q : ℝ) * x) := by
  sorry

theorem chapter10_interval_mul_nonnegative_valid
    {I J : Chapter10RationalInterval}
    (hI : I.Valid) (hJ : J.Valid)
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower) :
    (chapter10IntervalMulNonnegative I J).Valid := by
  sorry

theorem chapter10_interval_mul_nonnegative_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower)
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalMulNonnegative I J).Contains (x * y) := by
  sorry

theorem chapter10_interval_add_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalAdd I J).Contains (x + y) := by
  sorry

theorem chapter10_interval_sub_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalSub I J).Contains (x - y) := by
  sorry

theorem chapter10_directed_subtraction_lower_bound
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.lower : ℝ) - (J.upper : ℝ) ≤ x - y := by
  sorry

theorem chapter10_directed_addition_lower_bound
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.lower : ℝ) + (J.lower : ℝ) ≤ x + y := by
  sorry

theorem chapter10_positive_quantity_uses_lower_endpoint
    {I : Chapter10RationalInterval} {x : ℝ}
    (hx : I.Contains x) :
    (I.lower : ℝ) ≤ x := by
  exact hx.1

def chapter10ExpPartialSum (r : ℝ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), r ^ j / (Nat.factorial j : ℝ)

def chapter10ExpRemainder (r : ℝ) (M : ℕ) : ℝ :=
  Real.exp r - chapter10ExpPartialSum r M

def chapter10ExpRemainderBound (r : ℝ) (M : ℕ) : ℝ :=
  r ^ (M + 1) / (Nat.factorial (M + 1) : ℝ) *
    (1 / (1 - r / (M + 2 : ℕ)))

theorem chapter10_exp_positive_taylor_tail_nonnegative
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    0 ≤ chapter10ExpRemainder r M ∧
      chapter10ExpRemainder r M ≤ chapter10ExpRemainderBound r M := by
  sorry

theorem chapter10_exp_positive_taylor_tail_strict
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (M : ℕ) :
    0 < chapter10ExpRemainder r M ∧
      chapter10ExpRemainder r M < chapter10ExpRemainderBound r M := by
  sorry

theorem chapter10_exp_positive_taylor_identity (r : ℝ) (M : ℕ) :
    Real.exp r = chapter10ExpPartialSum r M + chapter10ExpRemainder r M := by
  sorry

structure Chapter10ExpRangeReduction (r : ℝ) where
  scaleExponent : ℕ
  reduced : ℝ
  reduced_nonnegative : 0 ≤ reduced
  reduced_lt_one : reduced < 1
  relation : r = ((2 ^ scaleExponent : ℕ) : ℝ) * reduced

theorem chapter10_exp_range_reduction_exists
    {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Chapter10ExpRangeReduction r) := by
  sorry

theorem chapter10_exp_range_reduction_identity
    {r : ℝ} (R : Chapter10ExpRangeReduction r) :
    Real.exp r = (Real.exp R.reduced) ^ (2 ^ R.scaleExponent) := by
  sorry

structure Chapter10TaylorRemainderCertificate where
  reducedArgument : ℝ
  unusedIntervalWidth : ℝ
  reduced_nonnegative : 0 ≤ reducedArgument
  reduced_lt_one : reducedArgument < 1
  width_pos : 0 < unusedIntervalWidth
  twenty_term_bound :
    chapter10ExpRemainderBound reducedArgument 20 < unusedIntervalWidth

theorem chapter10_twenty_term_remainder_below_unused_width
    (C : Chapter10TaylorRemainderCertificate) :
    chapter10ExpRemainder C.reducedArgument 20 < C.unusedIntervalWidth := by
  exact lt_of_le_of_lt
    (chapter10_exp_positive_taylor_tail_nonnegative
      C.reduced_nonnegative C.reduced_lt_one 20).2
    C.twenty_term_bound

theorem chapter10_log_enclosure_propagates_before_exponentiation
    {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.log a ≤ Real.log x ∧ Real.log x ≤ Real.log b := by
  sorry

theorem chapter10_exp_enclosure_propagates_after_log_comparison
    {a b : ℝ} (hab : a ≤ b) : Real.exp a ≤ Real.exp b := by
  exact Real.exp_le_exp.mpr hab

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
