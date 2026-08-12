import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section02TheThresholdThreeSqrtThree

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

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
  sorry

theorem chapter11_archimedean_ledger_row_nine_halves :
    chapter11UnconditionalPoleCost (9 / 2 : ℝ) = 9 / 4 ∧
      1.23652 < chapter11B (9 / 2 : ℝ) ∧
      chapter11B (9 / 2 : ℝ) < 1.23653 ∧
      0.87395 < chapter11C (9 / 2 : ℝ) ∧
      chapter11C (9 / 2 : ℝ) < 0.87396 := by
  sorry

theorem chapter11_archimedean_ledger_row_six :
    chapter11UnconditionalPoleCost 6 = 3 ∧
      1.10355 < chapter11B 6 ∧
      chapter11B 6 < 1.10356 ∧
      0.80102 < chapter11C 6 ∧
      chapter11C 6 < 0.80103 := by
  sorry

def chapter11FiveFourthCeiling : ℝ :=
  Real.rpow 5 (5 / 4 : ℝ)

theorem chapter11_five_fourth_ceiling_decimal_enclosure :
    (7.4767439061 : ℝ) < chapter11FiveFourthCeiling ∧
      chapter11FiveFourthCeiling < 7.4767439062 := by
  sorry

theorem chapter11_five_fourth_ceiling_log_upper :
    Real.log chapter11FiveFourthCeiling < 2.011798 := by
  sorry

theorem chapter11_minkowski_never_crosses_five_fourth
    {n : ℕ} (hn : 0 < n) :
    chapter11MinkowskiFactor n < chapter11FiveFourthCeiling := by
  sorry

def chapter11FiveFourthLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (9 : ℝ) / 17 - 1.23653

theorem chapter11_five_fourth_log_endpoint_lower :
    (2.03544 : ℝ) < chapter11FiveFourthLogEndpoint := by
  sorry

theorem chapter11_five_fourth_degree_seventeen_log_expression_lower :
    (2.03544 : ℝ) <
      chapter11ExplicitFormulaLogExpression 17 (9 / 2 : ℝ) 0 := by
  sorry

theorem chapter11_five_fourth_degree_seventeen_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 17 ≤ chapter11Degree K) :
    (2.03544 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  sorry

theorem chapter11_five_fourth_degree_seventeen_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 17 ≤ chapter11Degree K) :
    (7.6556 : ℝ) < chapter11RootDiscriminant K := by
  sorry

theorem chapter11_five_fourth_ceiling_below_degree_seventeen_root_endpoint :
    chapter11FiveFourthCeiling < 7.6556 := by
  sorry

theorem chapter11_five_fourth_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 16 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
