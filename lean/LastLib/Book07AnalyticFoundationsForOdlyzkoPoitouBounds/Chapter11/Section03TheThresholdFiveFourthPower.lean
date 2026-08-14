import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
open Filter
open scoped Topology

/-! ## 11.3. The threshold `5^(5/4)` -/

def chapter11UnconditionalPoleCost (T : ℝ) : ℝ :=
  T / 2

theorem chapter11_unconditional_pole_cost_eq_half (T : ℝ) :
    chapter11UnconditionalPoleCost T = T / 2 :=
  rfl

/- These are the three rows of the finite archimedean ledger used below and
   again in §§11.4–11.5. -/
theorem chapter11_archimedean_ledger_row_seventeen_over_five :
    chapter11UnconditionalPoleCost (17 / 5 : ℝ) = 17 / 10 ∧
      1.39921 < chapter11B (17 / 5 : ℝ) ∧
      chapter11B (17 / 5 : ℝ) < 1.39923 ∧
      0.95921 < chapter11C (17 / 5 : ℝ) ∧
      chapter11C (17 / 5 : ℝ) < 0.95923 := by
  have h := Chapter10.chapter10_archimedean_ledger_row_seventeen_over_five
  constructor
  · norm_num [chapter11UnconditionalPoleCost]
  · rw [chapter11_B_eq_chapter10_BT, chapter11_C_eq_chapter10_CT]
    convert h.2 using 1
    all_goals norm_num [Chapter10.chapter10RowSeventeenOverFive]

theorem chapter11_archimedean_ledger_row_nine_halves :
    chapter11UnconditionalPoleCost (9 / 2 : ℝ) = 9 / 4 ∧
      1.23652 < chapter11B (9 / 2 : ℝ) ∧
      chapter11B (9 / 2 : ℝ) < 1.23653 ∧
      0.87395 < chapter11C (9 / 2 : ℝ) ∧
      chapter11C (9 / 2 : ℝ) < 0.87396 := by
  have h := Chapter10.chapter10_archimedean_ledger_row_nine_halves
  constructor
  · norm_num [chapter11UnconditionalPoleCost]
  · rw [chapter11_B_eq_chapter10_BT, chapter11_C_eq_chapter10_CT]
    convert h.2 using 1
    all_goals norm_num [Chapter10.chapter10RowNineHalves]

theorem chapter11_archimedean_ledger_row_six :
    chapter11UnconditionalPoleCost 6 = 3 ∧
      1.10355 < chapter11B 6 ∧
      chapter11B 6 < 1.10356 ∧
      0.80102 < chapter11C 6 ∧
      chapter11C 6 < 0.80103 := by
  have h := Chapter10.chapter10_archimedean_ledger_row_six
  constructor
  · norm_num [chapter11UnconditionalPoleCost]
  · rw [chapter11_B_eq_chapter10_BT, chapter11_C_eq_chapter10_CT]
    convert h.2 using 1
    all_goals norm_num [Chapter10.chapter10RowSix]

def chapter11FiveFourthCeiling : ℝ :=
  Real.rpow 5 (5 / 4 : ℝ)

theorem chapter11_five_fourth_ceiling_decimal_enclosure :
      (7.4767439061 : ℝ) < chapter11FiveFourthCeiling ∧
      chapter11FiveFourthCeiling < 7.4767439062 := by
  have hpow : chapter11FiveFourthCeiling ^ (4 : ℕ) = (3125 : ℝ) := by
    unfold chapter11FiveFourthCeiling
    calc
      (Real.rpow (5 : ℝ) (5 / 4 : ℝ)) ^ (4 : ℕ) =
          Real.rpow (Real.rpow (5 : ℝ) (5 / 4 : ℝ)) (4 : ℝ) := by
            exact (Real.rpow_natCast
              (Real.rpow (5 : ℝ) (5 / 4 : ℝ)) 4).symm
      _ = Real.rpow (5 : ℝ) ((5 / 4 : ℝ) * (4 : ℝ)) :=
        (Real.rpow_mul (by norm_num) (5 / 4 : ℝ) (4 : ℝ)).symm
      _ = (3125 : ℝ) := by norm_num [Real.rpow_natCast]
  have hnonneg : 0 ≤ chapter11FiveFourthCeiling := by
    unfold chapter11FiveFourthCeiling
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  constructor
  · apply lt_of_pow_lt_pow_left₀ 4 hnonneg
    rw [hpow]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 4 (by norm_num)
    rw [hpow]
    norm_num

theorem chapter11_five_fourth_ceiling_log_upper :
    Real.log chapter11FiveFourthCeiling < 2.011798 := by
  have hlog2id := Chapter10.chapter10_log_two_series_identity 9
  have hlog2rem := Chapter10.chapter10_log_two_series_remainder_bound 9
  have hlog2rem_upper :
      Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 9 ≤
        2 * |(1 / 3 : ℝ)| ^ (2 * 9 + 3) /
          (((2 * 9 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) :=
    (le_abs_self _).trans hlog2rem
  have hlog2upper : Real.log 2 < (0.6931471806 : ℝ) := by
    rw [hlog2id]
    calc
      Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 9 +
          Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 9 ≤
          Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 9 +
            2 * |(1 / 3 : ℝ)| ^ (2 * 9 + 3) /
              (((2 * 9 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) :=
        add_le_add_right hlog2rem_upper _
      _ < (0.6931471806 : ℝ) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
  have hlog54id := Chapter10.chapter10_log_series_identity (1 / 9 : ℝ) 2
  have hlog54arg :
      (1 + (1 / 9 : ℝ)) / (1 - (1 / 9 : ℝ)) = (5 / 4 : ℝ) := by
    norm_num
  have hlog54id' :
      Real.log (5 / 4 : ℝ) =
        Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 2 +
          Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 2 := by
    rw [← hlog54arg]
    exact hlog54id
  have hlog54rem := Chapter10.chapter10_log_series_remainder_bound
    (y := (1 / 9 : ℝ)) (by norm_num) 2
  have hlog54rem_upper :
      Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 2 ≤
        2 * |(1 / 9 : ℝ)| ^ (2 * 2 + 3) /
          (((2 * 2 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2)) :=
    (le_abs_self _).trans hlog54rem
  have hlog54upper : Real.log (5 / 4 : ℝ) < (0.2231435515 : ℝ) := by
    rw [hlog54id']
    calc
      Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 2 +
          Chapter10.chapter10LogRemainder (1 / 9 : ℝ) 2 ≤
          Chapter10.chapter10LogPartialSum (1 / 9 : ℝ) 2 +
            2 * |(1 / 9 : ℝ)| ^ (2 * 2 + 3) /
              (((2 * 2 + 3 : ℕ) : ℝ) * (1 - (1 / 9 : ℝ) ^ 2)) :=
        add_le_add_right hlog54rem_upper _
      _ < (0.2231435515 : ℝ) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
  have hlog5 : Real.log 5 <
      2 * (0.6931471806 : ℝ) + 0.2231435515 := by
    have hlog5eq : Real.log (5 : ℝ) =
        2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
      calc
        Real.log (5 : ℝ) = Real.log ((4 : ℝ) * (5 / 4 : ℝ)) := by norm_num
        _ = Real.log (4 : ℝ) + Real.log (5 / 4 : ℝ) := by
          rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          norm_num
    rw [hlog5eq]
    linarith
  unfold chapter11FiveFourthCeiling
  have hrpow : Real.rpow (5 : ℝ) (5 / 4 : ℝ) =
      Real.exp (Real.log (5 : ℝ) * (5 / 4 : ℝ)) :=
    Real.rpow_def_of_pos (x := (5 : ℝ)) (y := (5 / 4 : ℝ)) (by norm_num)
  rw [hrpow, Real.log_exp]
  nlinarith

theorem chapter11_minkowski_never_crosses_five_fourth
    {n : ℕ} (hn : 0 < n) :
    chapter11MinkowskiFactor n < chapter11FiveFourthCeiling := by
  rw [chapter11_minkowski_factor_of_pos n hn]
  have hev : ∀ᶠ m : ℕ in atTop,
      chapter02FactorialFactor n ≤ chapter02FactorialFactor m := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hm : 0 < m := lt_of_lt_of_le hn hnm
    exact chapter02_factorial_factor_monotone (by simpa using hn)
      (by simpa using hm) hnm
  have hle : chapter02FactorialFactor n ≤ Real.exp 2 :=
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => chapter02FactorialFactor n) atTop
          (𝓝 (chapter02FactorialFactor n)))
      chapter02_factorial_factor_tendsto hev
  have hlt : chapter02FactorialFactor n < chapter02FiveToFiveFourth :=
    hle.trans_lt chapter02_totally_real_limit_below_five_to_five_fourth
  simpa [chapter02FactorialFactor, chapter02FiveToFiveFourth,
    chapter11FiveFourthCeiling] using hlt

def chapter11FiveFourthLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (9 : ℝ) / 17 - 1.23653

theorem chapter11_five_fourth_log_endpoint_lower :
    (2.03544 : ℝ) < chapter11FiveFourthLogEndpoint := by
  have hlog2id := Chapter10.chapter10_log_two_series_identity 12
  have hlog2rem := Chapter10.chapter10_log_two_series_remainder_bound 12
  have hlog2rem_lower :
      -(2 * |(1 / 3 : ℝ)| ^ (2 * 12 + 3) /
          (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 12 := by
    have hneg := neg_le_abs (Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 12)
    linarith
  have hlog2lower : (0.6931471805599 : ℝ) < Real.log 2 := by
    rw [hlog2id]
    calc
      (0.6931471805599 : ℝ) <
          Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 12 -
            2 * |(1 / 3 : ℝ)| ^ (2 * 12 + 3) /
              (((2 * 12 + 3 : ℕ) : ℝ) * (1 - (1 / 3 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (1 / 3 : ℝ) 12 +
          Chapter10.chapter10LogRemainder (1 / 3 : ℝ) 12 := by
        linarith
  have hlog15id := Chapter10.chapter10_log_series_identity (1 / 5 : ℝ) 8
  have hlog15arg :
      (1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ)) = (3 / 2 : ℝ) := by
    norm_num
  have hlog15id' :
      Real.log (3 / 2 : ℝ) =
        Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 8 +
          Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 8 := by
    rw [← hlog15arg]
    exact hlog15id
  have hlog15rem := Chapter10.chapter10_log_series_remainder_bound
    (y := (1 / 5 : ℝ)) (by norm_num) 8
  have hlog15rem_lower :
      -(2 * |(1 / 5 : ℝ)| ^ (2 * 8 + 3) /
          (((2 * 8 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 8 := by
    have hneg := neg_le_abs (Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 8)
    linarith
  have hlog15lower : (0.40546510810815 : ℝ) < Real.log (3 / 2 : ℝ) := by
    rw [hlog15id']
    calc
      (0.40546510810815 : ℝ) <
          Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 8 -
            2 * |(1 / 5 : ℝ)| ^ (2 * 8 + 3) /
              (((2 * 8 + 3 : ℕ) : ℝ) * (1 - (1 / 5 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (1 / 5 : ℝ) 8 +
          Chapter10.chapter10LogRemainder (1 / 5 : ℝ) 8 := by
        linarith
  have hlogqid := Chapter10.chapter10_log_series_identity
    (471975511 / 20471975511 : ℝ) 4
  have hlogqarg :
      (1 + (471975511 / 20471975511 : ℝ)) /
          (1 - (471975511 / 20471975511 : ℝ)) =
        (10471975511 / 10000000000 : ℝ) := by
    norm_num
  have hlogqid' :
      Real.log (10471975511 / 10000000000 : ℝ) =
        Chapter10.chapter10LogPartialSum (471975511 / 20471975511 : ℝ) 4 +
          Chapter10.chapter10LogRemainder (471975511 / 20471975511 : ℝ) 4 := by
    rw [← hlogqarg]
    exact hlogqid
  have hlogqrem := Chapter10.chapter10_log_series_remainder_bound
    (y := (471975511 / 20471975511 : ℝ)) (by norm_num) 4
  have hlogqrem_lower :
      -(2 * |(471975511 / 20471975511 : ℝ)| ^ (2 * 4 + 3) /
          (((2 * 4 + 3 : ℕ) : ℝ) *
            (1 - (471975511 / 20471975511 : ℝ) ^ 2))) ≤
        Chapter10.chapter10LogRemainder (471975511 / 20471975511 : ℝ) 4 := by
    have hneg := neg_le_abs
      (Chapter10.chapter10LogRemainder (471975511 / 20471975511 : ℝ) 4)
    linarith
  have hlogqlower :
      (0.046117597089 : ℝ) < Real.log (10471975511 / 10000000000 : ℝ) := by
    rw [hlogqid']
    calc
      (0.046117597089 : ℝ) <
          Chapter10.chapter10LogPartialSum (471975511 / 20471975511 : ℝ) 4 -
            2 * |(471975511 / 20471975511 : ℝ)| ^ (2 * 4 + 3) /
              (((2 * 4 + 3 : ℕ) : ℝ) *
                (1 - (471975511 / 20471975511 : ℝ) ^ 2)) := by
        norm_num [Chapter10.chapter10LogPartialSum, Finset.sum_range_succ]
      _ ≤ Chapter10.chapter10LogPartialSum (471975511 / 20471975511 : ℝ) 4 +
          Chapter10.chapter10LogRemainder (471975511 / 20471975511 : ℝ) 4 := by
        linarith
  have hpi : (Chapter10.chapter10PiLower : ℝ) < Real.pi :=
    Chapter10.chapter10_pi_directed_bounds.1
  norm_num [Chapter10.chapter10PiLower] at hpi
  have hqpi :
      (10471975511 / 10000000000 : ℝ) < Real.pi / 3 := by
    nlinarith [hpi]
  have hA :
      (16 : ℝ) * (3 / 2 : ℝ) * (10471975511 / 10000000000 : ℝ) <
        8 * Real.pi := by
    nlinarith [hqpi]
  have hlogA :
      Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
          (10471975511 / 10000000000 : ℝ)) =
        4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (10471975511 / 10000000000 : ℝ) := by
    calc
      Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
          (10471975511 / 10000000000 : ℝ)) =
          Real.log ((16 : ℝ) * (3 / 2 : ℝ)) +
            Real.log (10471975511 / 10000000000 : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (16 : ℝ) + Real.log (3 / 2 : ℝ) +
            Real.log (10471975511 / 10000000000 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
            Real.log (10471975511 / 10000000000 : ℝ) := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
  have hlogprod :
      4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (10471975511 / 10000000000 : ℝ) <
        Real.log (8 * Real.pi) := by
    calc
      4 * Real.log 2 + Real.log (3 / 2 : ℝ) +
          Real.log (10471975511 / 10000000000 : ℝ) =
          Real.log ((16 : ℝ) * (3 / 2 : ℝ) *
            (10471975511 / 10000000000 : ℝ)) := hlogA.symm
      _ < Real.log (8 * Real.pi) := by
        exact Real.strictMonoOn_log
          (show (16 : ℝ) * (3 / 2 : ℝ) *
              (10471975511 / 10000000000 : ℝ) ∈ Set.Ioi 0 from
                Set.mem_Ioi.mpr (by positivity))
          (show 8 * Real.pi ∈ Set.Ioi 0 from
            Set.mem_Ioi.mpr (by positivity)) hA
  have hγ := Chapter10.chapter10_gamma_directed_bounds.1
  norm_num [Chapter10.chapter10GammaLower] at hγ
  unfold chapter11FiveFourthLogEndpoint
  nlinarith

theorem chapter11_five_fourth_degree_seventeen_log_expression_lower :
    (2.03544 : ℝ) <
      chapter11ExplicitFormulaLogExpression 17 (9 / 2 : ℝ) 0 := by
  have hB : chapter11B (9 / 2 : ℝ) ≤ (1.23653 : ℝ) :=
    (chapter11_archimedean_ledger_row_nine_halves).2.2.1.le
  have hbase := chapter11_explicit_formula_log_expression_ge_of_B_upper
    17 (9 / 2 : ℝ) 0 (1.23653 : ℝ) hB
  calc
    (2.03544 : ℝ) < chapter11FiveFourthLogEndpoint :=
      chapter11_five_fourth_log_endpoint_lower
    _ ≤ chapter11ExplicitFormulaLogExpression 17 (9 / 2 : ℝ) 0 := by
      unfold chapter11FiveFourthLogEndpoint
      convert hbase using 1; norm_num

theorem chapter11_five_fourth_degree_seventeen_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 17 ≤ chapter11Degree K) :
    (2.03544 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  have hbase := chapter11_five_fourth_degree_seventeen_log_expression_lower
  have hdegree_mono := chapter11_explicit_formula_log_expression_mono_degree
    (hm := by norm_num) hdegree (9 / 2 : ℝ) (by norm_num) 0
  have hC : chapter11C (9 / 2 : ℝ) ≤ Real.pi / 2 := by
    rw [chapter11_C_eq_chapter10_CT, Chapter10.chapter10_CT_eq_chapter09_CT]
    exact (Chapter09.chapter09_unconditional_archimedean_C_lt_pi_div_two
      (by norm_num)).le
  have hα := chapter11_real_proportion_nonneg K
  have hsignature := chapter11_explicit_formula_log_expression_mono_signature
    (chapter11Degree K) (9 / 2 : ℝ) 0 (chapter11RealProportion K) hα hC
  have hbound := chapter11_explicit_formula_log_root_discriminant_bound
    K (9 / 2 : ℝ) (by norm_num)
  calc
    (2.03544 : ℝ) <
        chapter11ExplicitFormulaLogExpression 17 (9 / 2 : ℝ) 0 := hbase
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K)
        (9 / 2 : ℝ) 0 := hdegree_mono
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K)
        (9 / 2 : ℝ) (chapter11RealProportion K) := hsignature
    _ ≤ Real.log (chapter11RootDiscriminant K) := by
      exact hbound

theorem chapter11_five_fourth_degree_seventeen_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 17 ≤ chapter11Degree K) :
    (7.6556 : ℝ) < chapter11RootDiscriminant K := by
  have hexp1 : (2.7182818 : ℝ) < Real.exp 1 := by
    calc
      (2.7182818 : ℝ) <
          ∑ k ∈ Finset.range 11,
            (1 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp 1 := by
        simpa using (Real.sum_le_exp_of_nonneg (x := (1 : ℝ))
          (by norm_num) 11)
  have hexp2 : (2.7182818 : ℝ) ^ 2 < Real.exp 2 := by
    have hmul₁ : (2.7182818 : ℝ) * 2.7182818 <
        Real.exp 1 * 2.7182818 :=
      mul_lt_mul_of_pos_right hexp1 (by norm_num)
    have hmul₂ : Real.exp 1 * 2.7182818 < Real.exp 1 * Real.exp 1 :=
      mul_lt_mul_of_pos_left hexp1 (Real.exp_pos 1)
    calc
      (2.7182818 : ℝ) ^ 2 < Real.exp 1 * Real.exp 1 := by
        simpa [pow_two] using hmul₁.trans hmul₂
      _ = Real.exp 2 := by
        rw [← Real.exp_add]
        norm_num
  have hexpx :
      1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
          (0.03544 : ℝ) ^ 3 / 6 < Real.exp (0.03544 : ℝ) := by
    calc
      1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
          (0.03544 : ℝ) ^ 3 / 6 <
          ∑ k ∈ Finset.range 5,
            (0.03544 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp (0.03544 : ℝ) := by
        simpa using (Real.sum_le_exp_of_nonneg (x := (0.03544 : ℝ))
          (by norm_num) 5)
  have hexplower : (7.6556 : ℝ) < Real.exp (2.03544 : ℝ) := by
    calc
      (7.6556 : ℝ) <
          (2.7182818 : ℝ) ^ 2 *
            (1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
              (0.03544 : ℝ) ^ 3 / 6) := by
        norm_num
      _ < Real.exp 2 * Real.exp (0.03544 : ℝ) := by
        have hmul₁ :
            (2.7182818 : ℝ) ^ 2 *
                (1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
                  (0.03544 : ℝ) ^ 3 / 6) <
              Real.exp 2 *
                (1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
                  (0.03544 : ℝ) ^ 3 / 6) :=
          mul_lt_mul_of_pos_right hexp2 (by positivity)
        have hmul₂ :
            Real.exp 2 *
                (1 + (0.03544 : ℝ) + (0.03544 : ℝ) ^ 2 / 2 +
                  (0.03544 : ℝ) ^ 3 / 6) <
              Real.exp 2 * Real.exp (0.03544 : ℝ) :=
          mul_lt_mul_of_pos_left hexpx (by positivity)
        exact hmul₁.trans hmul₂
      _ = Real.exp (2.03544 : ℝ) := by
        rw [← Real.exp_add]
        norm_num
  have hlog := chapter11_five_fourth_degree_seventeen_log_lower K hdegree
  calc
    (7.6556 : ℝ) < Real.exp (2.03544 : ℝ) := hexplower
    _ < Real.exp (Real.log (chapter11RootDiscriminant K)) :=
      Real.exp_lt_exp.mpr hlog
    _ = chapter11RootDiscriminant K :=
      Real.exp_log (chapter11_root_discriminant_pos K)

theorem chapter11_five_fourth_ceiling_below_degree_seventeen_root_endpoint :
    chapter11FiveFourthCeiling < 7.6556 := by
  exact (chapter11_five_fourth_ceiling_decimal_enclosure.2).trans
    (by norm_num : (7.4767439062 : ℝ) < 7.6556)

theorem chapter11_five_fourth_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 16 := by
  by_contra hnot
  have hdegree : 17 ≤ chapter11Degree K := by omega
  have hroot := chapter11_five_fourth_degree_seventeen_root_lower K hdegree
  have hupper : chapter11RootDiscriminant K < 7.6556 :=
    hceiling.trans chapter11_five_fourth_ceiling_below_degree_seventeen_root_endpoint
  exact (lt_irrefl (7.6556 : ℝ)) (hroot.trans hupper)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
