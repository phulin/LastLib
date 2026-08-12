import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section03TheThresholdFiveFourthPower

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

/-! ## 11.4. The two-prime threshold `3^(3/2) 2^(2/3)` -/

def chapter11TwoPrimeCeiling : ℝ :=
  Real.rpow 3 (3 / 2 : ℝ) * Real.rpow 2 (2 / 3 : ℝ)

theorem chapter11_two_prime_ceiling_decimal_enclosure :
    (8.248377821991616 : ℝ) < chapter11TwoPrimeCeiling ∧
      chapter11TwoPrimeCeiling < 8.248377821991617 := by
  sorry

theorem chapter11_two_prime_ceiling_log_eq :
    Real.log chapter11TwoPrimeCeiling =
      (3 / 2 : ℝ) * Real.log 3 + (2 / 3 : ℝ) * Real.log 2 := by
  sorry

theorem chapter11_two_prime_ceiling_log_upper :
    Real.log chapter11TwoPrimeCeiling < 2.110016553375462 := by
  sorry

def chapter11TwoPrimeLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (12 : ℝ) / 21 - 1.10356

theorem chapter11_two_prime_log_endpoint_lower :
    (2.126398521002197 : ℝ) < chapter11TwoPrimeLogEndpoint := by
  sorry

theorem chapter11_two_prime_log_margin :
    (0.016381967626735 : ℝ) <
      chapter11TwoPrimeLogEndpoint - 2.110016553375462 := by
  sorry

theorem chapter11_two_prime_degree_twenty_one_log_expression_lower :
    (2.126398521002197 : ℝ) <
      chapter11ExplicitFormulaLogExpression 21 6 0 := by
  sorry

theorem chapter11_two_prime_degree_twenty_one_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 21 ≤ chapter11Degree K) :
    (2.126398521002197 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  sorry

theorem chapter11_two_prime_degree_twenty_one_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 21 ≤ chapter11Degree K) :
    (8.38461535304387 : ℝ) < chapter11RootDiscriminant K := by
  sorry

theorem chapter11_two_prime_ceiling_below_degree_twenty_one_root_endpoint :
    chapter11TwoPrimeCeiling < 8.38461535304387 := by
  sorry

theorem chapter11_two_prime_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11TwoPrimeCeiling) :
    chapter11Degree K ≤ 20 := by
  sorry

theorem chapter11_two_prime_ceiling_does_not_cross_degree_fifty_three_minkowski :
    ¬ chapter11TwoPrimeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  sorry

theorem chapter11_three_sqrt_three_lt_two_prime_ceiling :
    chapter11ThreeSqrtThreeCeiling < chapter11TwoPrimeCeiling := by
  sorry

/- (11.8a) is a separate certificate: it reuses the degree-21 crossing at the
   larger ceiling, so it does not erase the independent degree-53 geometric
   certificate from §11.2. -/
theorem chapter11_three_sqrt_three_explicit_formula_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 20 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
