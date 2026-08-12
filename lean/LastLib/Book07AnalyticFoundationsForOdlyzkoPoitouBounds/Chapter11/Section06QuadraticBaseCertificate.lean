import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section05TotallyRealCertificates

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11

noncomputable section

open Module

/-! ## 11.6. A quadratic-base certificate -/

def chapter11FourSqrtFiveCeiling : ℝ :=
  4 * Real.sqrt 5

theorem chapter11_four_sqrt_five_ceiling_eq :
    chapter11FourSqrtFiveCeiling = 4 * Real.sqrt 5 :=
  rfl

theorem chapter11_four_sqrt_five_is_positive :
    0 < chapter11FourSqrtFiveCeiling := by
  sorry

def chapter11QuadraticBaseDegreeRelation
    {F K : Type*} [Field F] [Field K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K] : Prop :=
  Module.finrank ℚ K = 2 * Module.finrank F K

theorem chapter11_quadratic_base_degree_relation
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2) :
    chapter11QuadraticBaseDegreeRelation (F := F) (K := K) := by
  sorry

theorem chapter11_quadratic_base_degree_even
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2) :
    Even (chapter11Degree K) := by
  sorry

def chapter11QuadraticBaseLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (12 : ℝ) / 24 - 1.10356

theorem chapter11_quadratic_base_log_endpoint_lower :
    (2.19782 : ℝ) < chapter11QuadraticBaseLogEndpoint := by
  sorry

theorem chapter11_quadratic_base_degree_twenty_four_log_expression_lower :
    (2.19782 : ℝ) <
      chapter11ExplicitFormulaLogExpression 24 6 0 := by
  sorry

theorem chapter11_quadratic_base_degree_twenty_four_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 24 ≤ chapter11Degree K) :
    (2.19782 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  sorry

theorem chapter11_quadratic_base_degree_twenty_four_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 24 ≤ chapter11Degree K) :
    (9.0053 : ℝ) < chapter11RootDiscriminant K := by
  sorry

theorem chapter11_four_sqrt_five_ceiling_below_degree_twenty_four_root_endpoint :
    chapter11FourSqrtFiveCeiling < 9.0053 := by
  sorry

theorem chapter11_quadratic_base_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    chapter11Degree K ≤ 23 := by
  sorry

theorem chapter11_quadratic_base_even_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling)
    (hEven : Even (chapter11Degree K)) :
    chapter11Degree K ≤ 22 := by
  sorry

theorem chapter11_quadratic_base_relative_degree_cutoff
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2)
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    Module.finrank F K ≤ 11 := by
  sorry

theorem chapter11_quadratic_base_absolute_and_relative_degree_cutoff
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2)
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    chapter11Degree K ≤ 22 ∧ Module.finrank F K ≤ 11 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
