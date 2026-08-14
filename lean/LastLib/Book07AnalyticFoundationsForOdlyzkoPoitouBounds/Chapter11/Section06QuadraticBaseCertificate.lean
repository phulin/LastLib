import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section03TheThresholdFiveFourthPower

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
  unfold chapter11FourSqrtFiveCeiling
  positivity

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
  unfold chapter11QuadraticBaseDegreeRelation
  have h := Module.finrank_mul_finrank ℚ F K
  rw [hF] at h
  exact h.symm

theorem chapter11_quadratic_base_degree_even
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2) :
    Even (chapter11Degree K) := by
  have hrel := chapter11_quadratic_base_degree_relation (F := F) (K := K) hF
  unfold chapter11QuadraticBaseDegreeRelation at hrel
  have halg : (‹Algebra ℚ K› : Algebra ℚ K) =
      (DivisionRing.toRatAlgebra : Algebra ℚ K) := Subsingleton.elim _ _
  refine ⟨Module.finrank F K, ?_⟩
  rw [halg] at hrel
  simpa [chapter11Degree, two_mul] using hrel

def chapter11QuadraticBaseLogEndpoint : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    (12 : ℝ) / 24 - 1.10356

theorem chapter11_quadratic_base_log_endpoint_lower :
    (2.19782 : ℝ) < chapter11QuadraticBaseLogEndpoint := by
  have hfive := chapter11_five_fourth_log_endpoint_lower
  unfold chapter11QuadraticBaseLogEndpoint at *
  unfold chapter11FiveFourthLogEndpoint at hfive
  nlinarith

theorem chapter11_quadratic_base_degree_twenty_four_log_expression_lower :
    (2.19782 : ℝ) <
      chapter11ExplicitFormulaLogExpression 24 6 0 := by
  have hrow := Chapter10.chapter10_archimedean_ledger_row_six
  have hB : chapter11B 6 ≤ (1.10356 : ℝ) := by
    rw [chapter11_B_eq_chapter10_BT]
    have hb := hrow.2.2.1
    have hb' : Chapter10.chapter10BT 6 < (1.10356 : ℝ) := by
      convert hb using 1
      norm_num [Chapter10.chapter10RowSix]
    exact hb'.le
  have hbase := chapter11_explicit_formula_log_expression_ge_of_B_upper
    24 6 0 (1.10356 : ℝ) hB
  calc
    (2.19782 : ℝ) < chapter11QuadraticBaseLogEndpoint :=
      chapter11_quadratic_base_log_endpoint_lower
    _ ≤ chapter11ExplicitFormulaLogExpression 24 6 0 := by
      unfold chapter11QuadraticBaseLogEndpoint
      convert hbase using 1; norm_num

theorem chapter11_quadratic_base_degree_twenty_four_log_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 24 ≤ chapter11Degree K) :
    (2.19782 : ℝ) < Real.log (chapter11RootDiscriminant K) := by
  have hbase := chapter11_quadratic_base_degree_twenty_four_log_expression_lower
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
    (2.19782 : ℝ) < chapter11ExplicitFormulaLogExpression 24 6 0 := hbase
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K) 6 0 :=
      hdegree_mono
    _ ≤ chapter11ExplicitFormulaLogExpression (chapter11Degree K) 6
        (chapter11RealProportion K) := hsignature
    _ ≤ Real.log (chapter11RootDiscriminant K) := hbound

theorem chapter11_quadratic_base_degree_twenty_four_root_lower
    (K : Type*) [Field K] [NumberField K]
    (hdegree : 24 ≤ chapter11Degree K) :
    (9.0053 : ℝ) < chapter11RootDiscriminant K := by
  have hexplower : (9.0053 : ℝ) < Real.exp (2.19782 : ℝ) := by
    calc
      (9.0053 : ℝ) <
          ∑ k ∈ Finset.range 12,
            (2.19782 : ℝ) ^ k / (Nat.factorial k : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial_succ]
      _ ≤ Real.exp (2.19782 : ℝ) := by
        simpa using (Real.sum_le_exp_of_nonneg (x := (2.19782 : ℝ))
          (by norm_num) 12)
  have hlog := chapter11_quadratic_base_degree_twenty_four_log_lower K hdegree
  calc
    (9.0053 : ℝ) < Real.exp (2.19782 : ℝ) := hexplower
    _ < Real.exp (Real.log (chapter11RootDiscriminant K)) :=
      Real.exp_lt_exp.mpr hlog
    _ = chapter11RootDiscriminant K :=
      Real.exp_log (chapter11_root_discriminant_pos K)

theorem chapter11_four_sqrt_five_ceiling_below_degree_twenty_four_root_endpoint :
    chapter11FourSqrtFiveCeiling < 9.0053 := by
  have hsq : chapter11FourSqrtFiveCeiling ^ (2 : ℕ) = (80 : ℝ) := by
    unfold chapter11FourSqrtFiveCeiling
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  apply lt_of_pow_lt_pow_left₀ 2 (by norm_num : (0 : ℝ) ≤ 9.0053)
  rw [hsq]
  norm_num

theorem chapter11_quadratic_base_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    chapter11Degree K ≤ 23 := by
  by_contra hnot
  have hdegree : 24 ≤ chapter11Degree K := by omega
  have hroot := chapter11_quadratic_base_degree_twenty_four_root_lower K hdegree
  have hupper : chapter11RootDiscriminant K < 9.0053 :=
    hceiling.trans chapter11_four_sqrt_five_ceiling_below_degree_twenty_four_root_endpoint
  exact (lt_irrefl (9.0053 : ℝ)) (hroot.trans hupper)

theorem chapter11_quadratic_base_even_degree_cutoff
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling)
    (hEven : Even (chapter11Degree K)) :
    chapter11Degree K ≤ 22 := by
  have hdegree := chapter11_quadratic_base_degree_cutoff K hceiling
  rcases hEven with ⟨m, hm⟩
  omega

theorem chapter11_quadratic_base_relative_degree_cutoff
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2)
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    Module.finrank F K ≤ 11 := by
  have hEven := chapter11_quadratic_base_degree_even (F := F) (K := K) hF
  have habs := chapter11_quadratic_base_even_degree_cutoff K hceiling hEven
  have hrel := chapter11_quadratic_base_degree_relation (F := F) (K := K) hF
  unfold chapter11QuadraticBaseDegreeRelation at hrel
  have halg : (‹Algebra ℚ K› : Algebra ℚ K) =
      (DivisionRing.toRatAlgebra : Algebra ℚ K) := Subsingleton.elim _ _
  have hrel' : chapter11Degree K = 2 * Module.finrank F K := by
    rw [halg] at hrel
    simpa [chapter11Degree] using hrel
  omega

theorem chapter11_quadratic_base_absolute_and_relative_degree_cutoff
    {F K : Type*} [Field F] [Field K] [NumberField K]
    [Algebra ℚ F] [Algebra F K] [Algebra ℚ K]
    [IsScalarTower ℚ F K] [FiniteDimensional ℚ F]
    [FiniteDimensional F K]
    (hF : Module.finrank ℚ F = 2)
    (hceiling : chapter11RootDiscriminant K < chapter11FourSqrtFiveCeiling) :
    chapter11Degree K ≤ 22 ∧ Module.finrank F K ≤ 11 := by
  constructor
  · exact chapter11_quadratic_base_even_degree_cutoff K hceiling
      (chapter11_quadratic_base_degree_even hF)
  · exact chapter11_quadratic_base_relative_degree_cutoff hF hceiling

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
