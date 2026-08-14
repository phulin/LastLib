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
  simpa [Chapter10RationalInterval.Valid, chapter10IntervalAdd] using
    (add_le_add hI hJ)

theorem chapter10_interval_sub_valid
    {I J : Chapter10RationalInterval} (hI : I.Valid) (hJ : J.Valid) :
    (chapter10IntervalSub I J).Valid := by
  have hI' : I.lower ≤ I.upper := hI
  have hJ' : J.lower ≤ J.upper := hJ
  have hsub : I.lower - J.upper ≤ I.upper - J.lower := by
    linarith
  simpa [Chapter10RationalInterval.Valid, chapter10IntervalSub] using
    hsub

theorem chapter10_interval_scale_nonnegative_valid
    {q : ℚ} {I : Chapter10RationalInterval}
    (hq : 0 ≤ q) (hI : I.Valid) :
    (chapter10IntervalScaleNonnegative q I).Valid := by
  simpa [Chapter10RationalInterval.Valid, chapter10IntervalScaleNonnegative] using
    (mul_le_mul_of_nonneg_left hI hq)

theorem chapter10_interval_scale_nonnegative_contains
    {q : ℚ} {I : Chapter10RationalInterval} {x : ℝ}
    (hq : 0 ≤ q) (hx : I.Contains x) :
    (chapter10IntervalScaleNonnegative q I).Contains ((q : ℝ) * x) := by
  change ((q * I.lower : ℚ) : ℝ) ≤ (q : ℝ) * x ∧
    (q : ℝ) * x ≤ ((q * I.upper : ℚ) : ℝ)
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · simpa using mul_le_mul_of_nonneg_left hx.1 hqR
  · simpa using mul_le_mul_of_nonneg_left hx.2 hqR

theorem chapter10_interval_mul_nonnegative_valid
    {I J : Chapter10RationalInterval}
    (hI : I.Valid) (hJ : J.Valid)
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower) :
    (chapter10IntervalMulNonnegative I J).Valid := by
  simpa [Chapter10RationalInterval.Valid, chapter10IntervalMulNonnegative] using
    (mul_le_mul hI hJ hJ0 (le_trans hI0 hI))

theorem chapter10_interval_mul_nonnegative_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower)
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalMulNonnegative I J).Contains (x * y) := by
  change ((I.lower * J.lower : ℚ) : ℝ) ≤ x * y ∧
    x * y ≤ ((I.upper * J.upper : ℚ) : ℝ)
  have hI0R : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI0
  have hJ0R : (0 : ℝ) ≤ J.lower := by exact_mod_cast hJ0
  have hxlower : (0 : ℝ) ≤ x := le_trans hI0R hx.1
  have hylower : (0 : ℝ) ≤ y := le_trans hJ0R hy.1
  have hxupper : x ≤ (I.upper : ℝ) := hx.2
  have hyupper : y ≤ (J.upper : ℝ) := hy.2
  constructor
  · simpa using mul_le_mul hx.1 hy.1 hJ0R hxlower
  · simpa using mul_le_mul hxupper hyupper hylower
      (le_trans hxlower hxupper)

theorem chapter10_interval_add_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalAdd I J).Contains (x + y) := by
  change ((I.lower + J.lower : ℚ) : ℝ) ≤ x + y ∧
    x + y ≤ ((I.upper + J.upper : ℚ) : ℝ)
  constructor
  · simpa using add_le_add hx.1 hy.1
  · simpa using add_le_add hx.2 hy.2

theorem chapter10_interval_sub_contains
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (chapter10IntervalSub I J).Contains (x - y) := by
  change ((I.lower - J.upper : ℚ) : ℝ) ≤ x - y ∧
    x - y ≤ ((I.upper - J.lower : ℚ) : ℝ)
  constructor
  · simpa using sub_le_sub hx.1 hy.2
  · simpa using sub_le_sub hx.2 hy.1

theorem chapter10_directed_subtraction_lower_bound
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.lower : ℝ) - (J.upper : ℝ) ≤ x - y := by
  exact sub_le_sub hx.1 hy.2

theorem chapter10_directed_addition_lower_bound
    {I J : Chapter10RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.lower : ℝ) + (J.lower : ℝ) ≤ x + y := by
  exact add_le_add hx.1 hy.1

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
  let k : ℕ := M + 1
  let a : ℕ → ℝ := fun n => r ^ n / (Nat.factorial n : ℝ)
  have hexp : HasSum a (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [a] using (NormedSpace.expSeries_div_hasSum_exp r)
  have htail : HasSum
      (fun i : ℕ => r ^ (i + k) / (Nat.factorial (i + k) : ℝ))
      (chapter10ExpRemainder r M) := by
    simpa [a, k, chapter10ExpRemainder, chapter10ExpPartialSum] using
      ((hasSum_nat_add_iff' k).2 hexp)
  let q : ℝ := r / ((M + 2 : ℕ) : ℝ)
  let C : ℝ := r ^ k / (Nat.factorial k : ℝ)
  let g : ℕ → ℝ := fun i => C * q ^ i
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hr0 (by positivity)
  have hM2 : (1 : ℝ) < (M + 2 : ℕ) := by
    exact_mod_cast (show 1 < M + 2 by omega)
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_one (by positivity)).2
    exact lt_trans hr1 hM2
  have hgeom : HasSum (fun i : ℕ => q ^ i) (1 - q)⁻¹ :=
    hasSum_geometric_of_lt_one hq0 hq1
  have hmajor : HasSum (fun i : ℕ => C * q ^ i) (C * (1 - q)⁻¹) :=
    hgeom.mul_left C
  have hform : ∀ i : ℕ,
      a (i + 1 + k) = a (i + k) * (r / ((i + k + 1 : ℕ) : ℝ)) := by
    intro i
    dsimp [a]
    rw [show i + 1 + k = (i + k) + 1 by omega,
      pow_succ, Nat.factorial_succ]
    field_simp [Nat.factorial_ne_zero]
    push_cast
    ring
  have hterm : ∀ i : ℕ, a (i + k) ≤ g i := by
    intro i
    induction i with
    | zero =>
        simp [a, g, C]
    | succ i ih =>
        have hden : ((M + 2 : ℕ) : ℝ) ≤ ((i + k + 1 : ℕ) : ℝ) := by
          have hden_nat : M + 2 ≤ i + k + 1 := by
            dsimp [k]
            omega
          exact_mod_cast hden_nat
        have hinv :
            1 / ((i + k + 1 : ℕ) : ℝ) ≤ 1 / ((M + 2 : ℕ) : ℝ) :=
          one_div_le_one_div_of_le (by positivity) hden
        have hratio : r / ((i + k + 1 : ℕ) : ℝ) ≤ q := by
          dsimp [q]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) hr0
        rw [show Nat.succ i + k = i + 1 + k by rfl, hform i]
        calc
          a (i + k) * (r / ((i + k + 1 : ℕ) : ℝ)) ≤
              g i * (r / ((i + k + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
          _ ≤ g i * q :=
            mul_le_mul_of_nonneg_left hratio (by
              dsimp [g, C, q]
              positivity)
          _ = g (i + 1) := by
            dsimp [g]
            rw [pow_succ]
            ring
  have hterm_nonneg : ∀ i : ℕ,
      0 ≤ r ^ (i + k) / (Nat.factorial (i + k) : ℝ) := by
    intro i
    exact div_nonneg (pow_nonneg hr0 _) (by positivity)
  have hsumterm : Summable
      (fun i : ℕ => r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by
    apply Summable.of_norm_bounded_eventually_nat hmajor.summable
    filter_upwards [] with i
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg i)]
    exact hterm i
  have hrem_nonneg : 0 ≤ chapter10ExpRemainder r M := by
    rw [← htail.tsum_eq]
    exact tsum_nonneg hterm_nonneg
  have hrem_bound : chapter10ExpRemainder r M ≤ C * (1 - q)⁻¹ := by
    rw [← htail.tsum_eq]
    calc
      (∑' i : ℕ, r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) ≤
          ∑' i : ℕ, g i := by
        simpa [a] using hsumterm.tsum_le_tsum hterm hmajor.summable
      _ = C * (1 - q)⁻¹ := hmajor.tsum_eq
  constructor
  · exact hrem_nonneg
  · simpa [chapter10ExpRemainderBound, C, q, k, div_eq_mul_inv] using hrem_bound

theorem chapter10_exp_positive_taylor_tail_strict
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (M : ℕ) :
    0 < chapter10ExpRemainder r M ∧
      chapter10ExpRemainder r M < chapter10ExpRemainderBound r M := by
  have hr0' : 0 ≤ r := le_of_lt hr0
  let k : ℕ := M + 1
  let a : ℕ → ℝ := fun n => r ^ n / (Nat.factorial n : ℝ)
  have hexp : HasSum a (Real.exp r) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [a] using (NormedSpace.expSeries_div_hasSum_exp r)
  have htail : HasSum
      (fun i : ℕ => r ^ (i + k) / (Nat.factorial (i + k) : ℝ))
      (chapter10ExpRemainder r M) := by
    simpa [a, k, chapter10ExpRemainder, chapter10ExpPartialSum] using
      ((hasSum_nat_add_iff' k).2 hexp)
  let q : ℝ := r / ((M + 2 : ℕ) : ℝ)
  let C : ℝ := r ^ k / (Nat.factorial k : ℝ)
  let g : ℕ → ℝ := fun i => C * q ^ i
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hr0' (by positivity)
  have hM2 : (1 : ℝ) < (M + 2 : ℕ) := by
    exact_mod_cast (show 1 < M + 2 by omega)
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_one (by positivity)).2
    exact lt_trans hr1 hM2
  have hgeom : HasSum (fun i : ℕ => q ^ i) (1 - q)⁻¹ :=
    hasSum_geometric_of_lt_one hq0 hq1
  have hmajor : HasSum (fun i : ℕ => C * q ^ i) (C * (1 - q)⁻¹) :=
    hgeom.mul_left C
  have hform : ∀ i : ℕ,
      a (i + 1 + k) = a (i + k) * (r / ((i + k + 1 : ℕ) : ℝ)) := by
    intro i
    dsimp [a]
    rw [show i + 1 + k = (i + k) + 1 by omega,
      pow_succ, Nat.factorial_succ]
    field_simp [Nat.factorial_ne_zero]
    push_cast
    ring
  have hterm : ∀ i : ℕ, a (i + k) ≤ g i := by
    intro i
    induction i with
    | zero =>
        simp [a, g, C]
    | succ i ih =>
        have hden : ((M + 2 : ℕ) : ℝ) ≤ ((i + k + 1 : ℕ) : ℝ) := by
          have hden_nat : M + 2 ≤ i + k + 1 := by
            dsimp [k]
            omega
          exact_mod_cast hden_nat
        have hinv :
            1 / ((i + k + 1 : ℕ) : ℝ) ≤ 1 / ((M + 2 : ℕ) : ℝ) :=
          one_div_le_one_div_of_le (by positivity) hden
        have hratio : r / ((i + k + 1 : ℕ) : ℝ) ≤ q := by
          dsimp [q]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) hr0'
        rw [show Nat.succ i + k = i + 1 + k by rfl, hform i]
        calc
          a (i + k) * (r / ((i + k + 1 : ℕ) : ℝ)) ≤
              g i * (r / ((i + k + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
          _ ≤ g i * q :=
            mul_le_mul_of_nonneg_left hratio (by
              dsimp [g, C, q]
              positivity)
          _ = g (i + 1) := by
            dsimp [g]
            rw [pow_succ]
            ring
  have hterm_nonneg : ∀ i : ℕ,
      0 ≤ r ^ (i + k) / (Nat.factorial (i + k) : ℝ) := by
    intro i
    exact div_nonneg (pow_nonneg hr0' _) (by positivity)
  have hsumterm : Summable
      (fun i : ℕ => r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) := by
    apply Summable.of_norm_bounded_eventually_nat hmajor.summable
    filter_upwards [] with i
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg i)]
    exact hterm i
  have hstrict :
      r ^ (2 + k) / (Nat.factorial (2 + k) : ℝ) < g 2 := by
    have hden : ((M + 2 : ℕ) : ℝ) < ((1 + k + 1 : ℕ) : ℝ) := by
      have hden_nat : M + 2 < 1 + k + 1 := by
        dsimp [k]
        omega
      exact_mod_cast hden_nat
    have hinv :
        1 / ((1 + k + 1 : ℕ) : ℝ) < 1 / ((M + 2 : ℕ) : ℝ) :=
      one_div_lt_one_div_of_lt (by positivity) hden
    have hratio : r / ((1 + k + 1 : ℕ) : ℝ) < q := by
      dsimp [q]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_pos_left (by simpa [one_div] using hinv) hr0
    have heq1 : a (1 + k) = g 1 := by
      rw [hform 0]
      dsimp [a, g, C, q, k]
      simp [Nat.add_assoc]
    change a (2 + k) < g 2
    rw [show 2 + k = 1 + 1 + k by omega, hform 1, heq1]
    calc
      g 1 * (r / ((1 + k + 1 : ℕ) : ℝ)) < g 1 * q :=
        mul_lt_mul_of_pos_left hratio (by
          dsimp [g, C, q]
          positivity)
      _ = g 2 := by
        dsimp [g]
        rw [pow_succ]
        ring
  have hrem_pos : 0 < chapter10ExpRemainder r M := by
    rw [← htail.tsum_eq]
    apply hsumterm.tsum_pos hterm_nonneg 0
    dsimp [k]
    positivity
  have hrem_strict : chapter10ExpRemainder r M < C * (1 - q)⁻¹ := by
    rw [← htail.tsum_eq]
    calc
      (∑' i : ℕ, r ^ (i + k) / (Nat.factorial (i + k) : ℝ)) <
          ∑' i : ℕ, g i := by
        exact hmajor.summable.tsum_lt_tsum_of_nonneg (g := g) (i := 2)
          hterm_nonneg hterm hstrict
      _ = C * (1 - q)⁻¹ := hmajor.tsum_eq
  constructor
  · exact hrem_pos
  · simpa [chapter10ExpRemainderBound, C, q, k, div_eq_mul_inv] using hrem_strict

theorem chapter10_exp_positive_taylor_identity (r : ℝ) (M : ℕ) :
    Real.exp r = chapter10ExpPartialSum r M + chapter10ExpRemainder r M := by
  simp [chapter10ExpRemainder]

structure Chapter10ExpRangeReduction (r : ℝ) where
  scaleExponent : ℕ
  reduced : ℝ
  reduced_nonnegative : 0 ≤ reduced
  reduced_lt_one : reduced < 1
  relation : r = ((2 ^ scaleExponent : ℕ) : ℝ) * reduced

theorem chapter10_exp_range_reduction_exists
    {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (Chapter10ExpRangeReduction r) := by
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hpow : n ≤ 2 ^ n :=
    (Nat.lt_pow_self (show 1 < 2 by decide)).le
  have hnp : r < ((2 ^ n : ℕ) : ℝ) := by
    exact lt_of_lt_of_le hn (by exact_mod_cast hpow)
  have hp : 0 < ((2 ^ n : ℕ) : ℝ) := by positivity
  refine ⟨⟨n, r / ((2 ^ n : ℕ) : ℝ),
    div_nonneg hr hp.le, (div_lt_one hp).2 hnp, ?_⟩⟩
  field_simp [ne_of_gt hp]

theorem chapter10_exp_range_reduction_identity
    {r : ℝ} (R : Chapter10ExpRangeReduction r) :
    Real.exp r = (Real.exp R.reduced) ^ (2 ^ R.scaleExponent) := by
  calc
    Real.exp r =
        Real.exp (((2 ^ R.scaleExponent : ℕ) : ℝ) * R.reduced) :=
      congrArg Real.exp R.relation
    _ = (Real.exp R.reduced) ^ (2 ^ R.scaleExponent) := by
      simpa using (Real.exp_nat_mul R.reduced (2 ^ R.scaleExponent))

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
  constructor
  · exact Real.log_le_log ha hax
  · exact Real.log_le_log (lt_of_lt_of_le ha hax) hxb

theorem chapter10_exp_enclosure_propagates_after_log_comparison
    {a b : ℝ} (hab : a ≤ b) : Real.exp a ≤ Real.exp b := by
  exact Real.exp_le_exp.mpr hab

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10
