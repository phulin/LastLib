import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section01TheThresholdFour
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section02TheThresholdThreeSqrtThree
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section03TheThresholdFiveFourthPower
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section04TheTwoPrimeThreshold

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open NumberField
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02

/-! ## 11.5. Totally real certificates -/

def chapter11TotallyRealFiveFourthLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2 -
    (34 : ℝ) / 35 - 1.39923 - 0.95923

theorem chapter11_totally_real_five_fourth_log_endpoint_lower :
    (2.04229 : ℝ) < chapter11TotallyRealFiveFourthLogEndpoint ∧
      (5 / 4 : ℝ) * Real.log 5 < chapter11TotallyRealFiveFourthLogEndpoint := by
  have htwo := chapter11_two_prime_log_endpoint_lower
  have hpi : (Chapter10.chapter10PiLower : ℝ) < Real.pi :=
    Chapter10.chapter10_pi_directed_bounds.1
  have htotal : (2.04229 : ℝ) < chapter11TotallyRealFiveFourthLogEndpoint := by
    unfold chapter11TotallyRealFiveFourthLogEndpoint at *
    unfold chapter11TwoPrimeLogEndpoint at htwo
    norm_num [Chapter10.chapter10PiLower] at hpi
    nlinarith
  have hlogCeq : Real.log chapter11FiveFourthCeiling =
      (5 / 4 : ℝ) * Real.log 5 := by
    unfold chapter11FiveFourthCeiling
    have hrpow : Real.rpow (5 : ℝ) (5 / 4 : ℝ) =
        Real.exp (Real.log (5 : ℝ) * (5 / 4 : ℝ)) :=
      Real.rpow_def_of_pos (x := (5 : ℝ)) (y := (5 / 4 : ℝ)) (by norm_num)
    rw [hrpow, Real.log_exp]
    ring
  have hlogC := chapter11_five_fourth_ceiling_log_upper
  rw [hlogCeq] at hlogC
  constructor
  · exact htotal
  · nlinarith

theorem chapter11_totally_real_degree_seven_log_expression_lower :
    (2.04229 : ℝ) <
      chapter11ExplicitFormulaLogExpression 7 (17 / 5 : ℝ) 1 := by
  have hrow := chapter11_archimedean_ledger_row_seventeen_over_five
  have hB : chapter11B (17 / 5 : ℝ) ≤ (1.39923 : ℝ) :=
    hrow.2.2.1.le
  have hC : chapter11C (17 / 5 : ℝ) ≤ (0.95923 : ℝ) :=
    hrow.2.2.2.2.le
  have hbase := chapter11_explicit_formula_log_expression_ge_of_B_upper
    7 (17 / 5 : ℝ) 1 (1.39923 : ℝ) hB
  have hendpoint := chapter11_totally_real_five_fourth_log_endpoint_lower.1
  calc
    (2.04229 : ℝ) < chapter11TotallyRealFiveFourthLogEndpoint := hendpoint
    _ ≤ chapter11ExplicitFormulaLogExpression 7 (17 / 5 : ℝ) 1 := by
      unfold chapter11TotallyRealFiveFourthLogEndpoint
      nlinarith [hbase, hC]

theorem chapter11_totally_real_degree_seven_log_lower
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hdegree : 7 ≤ chapter11Degree K) :
    (2.04229 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  have hbase := chapter11_totally_real_degree_seven_log_expression_lower
  have hdegree_mono := chapter11_explicit_formula_log_expression_mono_degree
    (hm := by norm_num) hdegree (17 / 5 : ℝ) (by norm_num) 1
  have hcomplex : chapter02ComplexPlaces K = 0 :=
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K
  have hreal : chapter02RealPlaces K = chapter02Degree K := by
    simpa [hcomplex] using (chapter02_signature_degree K)
  have hdegpos : 0 < (chapter02Degree K : ℝ) := by
    exact_mod_cast (chapter11_degree_pos K)
  have hα : chapter11RealProportion K = 1 := by
    unfold chapter11RealProportion
    change (chapter02RealPlaces K : ℝ) / (chapter02Degree K : ℝ) = 1
    rw [hreal, div_self (ne_of_gt hdegpos)]
  have hbound := chapter11_explicit_formula_log_root_discriminant_bound
    K (17 / 5 : ℝ) (by norm_num)
  calc
    (2.04229 : ℝ) <
        chapter11ExplicitFormulaLogExpression 7 (17 / 5 : ℝ) 1 := hbase
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K)
        (17 / 5 : ℝ) 1 := hdegree_mono
    _ = chapter11ExplicitFormulaLogExpression (chapter11Degree K)
        (17 / 5 : ℝ) (chapter11RealProportion K) := by rw [hα]
    _ ≤ Real.log (chapter11RootDiscriminant K) := hbound

theorem chapter11_totally_real_degree_seven_root_exceeds_five_fourth
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hdegree : 7 ≤ chapter11Degree K) :
    chapter11FiveFourthCeiling < chapter11RootDiscriminant K := by
  have hCpos : 0 < chapter11FiveFourthCeiling := by
    unfold chapter11FiveFourthCeiling
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hlogC : Real.log chapter11FiveFourthCeiling <
      (2.04229 : ℝ) := by
    exact lt_trans chapter11_five_fourth_ceiling_log_upper (by norm_num)
  have hrootlog := chapter11_totally_real_degree_seven_log_lower K hdegree
  have hexp : chapter11FiveFourthCeiling <
      Real.exp (2.04229 : ℝ) := by
    calc
      chapter11FiveFourthCeiling =
          Real.exp (Real.log chapter11FiveFourthCeiling) :=
        (Real.exp_log hCpos).symm
      _ < Real.exp (2.04229 : ℝ) := Real.exp_lt_exp.mpr hlogC
  calc
    chapter11FiveFourthCeiling < Real.exp (2.04229 : ℝ) := hexp
    _ < Real.exp (Real.log (chapter11RootDiscriminant K)) :=
      Real.exp_lt_exp.mpr hrootlog
    _ = chapter11RootDiscriminant K :=
      Real.exp_log (chapter11_root_discriminant_pos K)

theorem chapter11_totally_real_five_fourth_degree_cutoff
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 6 := by
  by_contra hnot
  have hdegree : 7 ≤ chapter11Degree K := by omega
  have hroot := chapter11_totally_real_degree_seven_root_exceeds_five_fourth K hdegree
  exact (lt_irrefl (chapter11FiveFourthCeiling)) (hroot.trans hceiling)

/- The three totally real caps are exposed together for downstream ledgers. -/
theorem chapter11_totally_real_basic_ceiling_caps
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    (chapter11RootDiscriminant K < 4 → chapter11Degree K ≤ 5) ∧
      (chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling →
        chapter11Degree K ≤ 12) ∧
      (chapter11RootDiscriminant K < chapter11FiveFourthCeiling →
        chapter11Degree K ≤ 6) := by
  constructor
  · exact fun hceiling => chapter11_minkowski_degree_six_totally_real_cutoff K hceiling
  constructor
  · exact fun hceiling => chapter11_minkowski_degree_thirteen_totally_real_cutoff K hceiling
  · exact fun hceiling => chapter11_totally_real_five_fourth_degree_cutoff K hceiling

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
