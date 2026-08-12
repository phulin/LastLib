import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section04TheTwoPrimeThreshold

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open NumberField

/-! ## 11.5. Totally real certificates -/

def chapter11TotallyRealFiveFourthLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2 -
    (34 : ℝ) / 35 - 1.39923 - 0.95923

theorem chapter11_totally_real_five_fourth_log_endpoint_lower :
    (2.04229 : ℝ) < chapter11TotallyRealFiveFourthLogEndpoint ∧
      (5 / 4 : ℝ) * Real.log 5 < chapter11TotallyRealFiveFourthLogEndpoint := by
  sorry

theorem chapter11_totally_real_degree_seven_log_expression_lower :
    (2.04229 : ℝ) <
      chapter11ExplicitFormulaLogExpression 7 (17 / 5 : ℝ) 1 := by
  sorry

theorem chapter11_totally_real_degree_seven_log_lower
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hdegree : 7 ≤ chapter11Degree K) :
    (2.04229 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  sorry

theorem chapter11_totally_real_degree_seven_root_exceeds_five_fourth
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hdegree : 7 ≤ chapter11Degree K) :
    chapter11FiveFourthCeiling < chapter11RootDiscriminant K := by
  sorry

theorem chapter11_totally_real_five_fourth_degree_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 6 := by
  sorry

/- The three totally real caps are exposed together for downstream ledgers. -/
theorem chapter11_totally_real_basic_ceiling_caps
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    (chapter11RootDiscriminant K < 4 → chapter11Degree K ≤ 5) ∧
      (chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling →
        chapter11Degree K ≤ 12) ∧
      (chapter11RootDiscriminant K < chapter11FiveFourthCeiling →
        chapter11Degree K ≤ 6) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
