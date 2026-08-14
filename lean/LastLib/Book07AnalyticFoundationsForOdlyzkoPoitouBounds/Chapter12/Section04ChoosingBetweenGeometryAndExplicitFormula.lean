import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Section01IntermediateSignatures
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section01TheThresholdFour
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section02TheThresholdThreeSqrtThree
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section03TheThresholdFiveFourthPower
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section04TheTwoPrimeThreshold

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ## 12.4. Choosing between geometry and the explicit formula -/

def chapter12GeometricRootDiscriminantBound
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter11GeometricRootDiscriminantBound K

def chapter12ExplicitFormulaRootBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter11ExplicitFormulaRootBound K T

def chapter12SafeRootDiscriminantBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  max (chapter12GeometricRootDiscriminantBound K)
    (chapter12ExplicitFormulaRootBound K T)

theorem chapter12_geometric_bound_le_safe
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter12GeometricRootDiscriminantBound K ≤
      chapter12SafeRootDiscriminantBound K T := by
  exact le_max_left _ _

theorem chapter12_explicit_bound_le_safe
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter12ExplicitFormulaRootBound K T ≤
      chapter12SafeRootDiscriminantBound K T := by
  exact le_max_right _ _

theorem chapter12_safe_bound_le_root_discriminant
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter12SafeRootDiscriminantBound K T ≤ chapter11RootDiscriminant K := by
  exact max_le
    (chapter11_geometric_root_discriminant_bound K)
    (chapter11_explicit_formula_root_discriminant_bound K T hT)

def chapter12GeometryWins
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Prop :=
  chapter12ExplicitFormulaRootBound K T ≤
    chapter12GeometricRootDiscriminantBound K

def chapter12ExplicitFormulaWins
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Prop :=
  chapter12GeometricRootDiscriminantBound K ≤
    chapter12ExplicitFormulaRootBound K T

theorem chapter12_safe_bound_eq_geometry_of_geometry_wins
    (K : Type*) [Field K] [NumberField K] {T : ℝ}
    (h : chapter12GeometryWins K T) :
    chapter12SafeRootDiscriminantBound K T =
      chapter12GeometricRootDiscriminantBound K := by
  exact max_eq_left h

theorem chapter12_safe_bound_eq_explicit_of_explicit_wins
    (K : Type*) [Field K] [NumberField K] {T : ℝ}
    (h : chapter12ExplicitFormulaWins K T) :
    chapter12SafeRootDiscriminantBound K T =
      chapter12ExplicitFormulaRootBound K T := by
  exact max_eq_right h

def chapter12GeometricAsymptoticConstant : ℝ :=
  (Real.pi / 4) * Real.exp 2

def chapter12UnconditionalAsymptoticConstant (α : ℝ) : ℝ :=
  chapter09UnconditionalAsymptoticConstant α

/- LOCAL_DEPENDENCY_GUESS: the factorial-factor limit used by the phrase
   “geometric limit” is the Stirling consequence Mₙ → e².  Chapter 11 has
   the finite factor and its monotonicity, but not this asymptotic bridge. -/
theorem chapter12_minkowski_factor_tendsto_exp_two :
    Tendsto (fun n : ℕ => chapter11MinkowskiFactor n) atTop (𝓝 (Real.exp 2)) := by
  have h : chapter11MinkowskiFactor =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.chapter02FactorialFactor := by
    funext n
    cases n with
    | zero =>
        simp [chapter11MinkowskiFactor,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.chapter02FactorialFactor]
    | succ n =>
        simp [chapter11MinkowskiFactor,
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.chapter02FactorialFactor]
  rw [h]
  exact LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02.chapter02_factorial_factor_tendsto

theorem chapter12_geometric_worst_signature_factor_tendsto :
    Tendsto
      (fun n : ℕ => (Real.pi / 4) * chapter11MinkowskiFactor n)
      atTop (𝓝 chapter12GeometricAsymptoticConstant) := by
  simpa [chapter12GeometricAsymptoticConstant] using
    (tendsto_const_nhds.mul chapter12_minkowski_factor_tendsto_exp_two)

theorem chapter12_explicit_unconditional_asymptotic_constant_larger
    {α : ℝ} (hα : 0 ≤ α) :
    chapter12GeometricAsymptoticConstant <
      chapter12UnconditionalAsymptoticConstant α := by
  have hgeom : chapter12GeometricAsymptoticConstant < (9 : ℝ) := by
    unfold chapter12GeometricAsymptoticConstant
    have hpi : Real.pi / 4 < (1 : ℝ) := by
      nlinarith [Real.pi_lt_four]
    have he2 : Real.exp (2 : ℝ) < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ)]
    calc
      (Real.pi / 4) * Real.exp 2 < 1 * Real.exp 2 :=
        mul_lt_mul_of_pos_right hpi (Real.exp_pos 2)
      _ < 9 := by simpa using he2
  have hzero : (9 : ℝ) < chapter09UnconditionalAsymptoticConstant 0 := by
    have hlow := chapter09_unconditional_endpoint_zero_directed_bounds.1
    have hrat : (9 : ℝ) < (chapter09UnconditionalEndpointZeroLower : ℝ) := by
      norm_num [chapter09UnconditionalEndpointZeroLower]
    exact hrat.trans (by simpa [chapter09UnconditionalEndpointZero,
      chapter09UnconditionalAsymptoticConstant] using hlow)
  have hmono : chapter09UnconditionalAsymptoticConstant 0 ≤
      chapter09UnconditionalAsymptoticConstant α := by
    unfold chapter09UnconditionalAsymptoticConstant
    apply mul_le_mul_of_nonneg_left
    · exact Real.exp_le_exp.mpr (by linarith)
    · positivity
  exact hgeom.trans (hzero.trans_le hmono)

theorem chapter12_independent_factorial_certificates :
    (4 : ℝ) < (Real.pi / 4) * chapter11MinkowskiFactor 12 ∧
      chapter11ThreeSqrtThreeCeiling <
        (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  exact ⟨chapter11_minkowski_factor_twelve_crosses_four_lower_endpoint,
    chapter11_three_sqrt_three_minkowski_crossing⟩

theorem chapter12_five_fourth_has_no_factorial_crossing
    {n : ℕ} (hn : 0 < n) :
    chapter11MinkowskiFactor n < chapter11FiveFourthCeiling := by
  exact chapter11_minkowski_never_crosses_five_fourth hn

theorem chapter12_five_fourth_requires_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 16 := by
  exact chapter11_five_fourth_degree_cutoff K hceiling

theorem chapter12_two_prime_requires_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11TwoPrimeCeiling) :
    chapter11Degree K ≤ 20 := by
  exact chapter11_two_prime_degree_cutoff K hceiling

theorem chapter12_two_prime_has_no_degree_fifty_three_factorial_crossing :
    ¬ chapter11TwoPrimeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  exact chapter11_two_prime_ceiling_does_not_cross_degree_fifty_three_minkowski

theorem chapter12_smaller_three_sqrt_three_has_two_prime_explicit_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 20 ∧ chapter11Degree K ≤ 52 := by
  exact ⟨chapter11_three_sqrt_three_explicit_formula_degree_cutoff K hceiling,
    chapter11_minkowski_degree_fifty_three_cutoff K hceiling⟩

def chapter12UnconditionalInfiniteDegreeLogExpression
    (T α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
      α * (Real.pi / 2) - chapter11B T - α * chapter11C T

def chapter12UnconditionalFiniteDegreeLogExpression
    (n : ℕ) (T α : ℝ) : ℝ :=
  chapter12AffineLogExpression n T α

def chapter12UnconditionalFiniteDegreeDeficit
    (n : ℕ) (T : ℝ) : ℝ :=
  2 * T / (n : ℝ)

theorem chapter12_unconditional_finite_degree_deficit_exact
    (n : ℕ) (T α : ℝ) :
    chapter12UnconditionalInfiniteDegreeLogExpression T α -
        chapter12UnconditionalFiniteDegreeLogExpression n T α =
      chapter12UnconditionalFiniteDegreeDeficit n T := by
  simp [chapter12UnconditionalInfiniteDegreeLogExpression,
    chapter12UnconditionalFiniteDegreeLogExpression,
    chapter12UnconditionalFiniteDegreeDeficit, chapter12AffineLogExpression,
    chapter12AffineLogBase, chapter12AffineLogSlope]
  ring

def chapter12UnconditionalLimitingLogExpression (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) - Real.log 2 + α

theorem chapter12_unconditional_limiting_log_expression_eq_log_constant
    (α : ℝ) :
    chapter12UnconditionalLimitingLogExpression α =
      Real.log (chapter12UnconditionalAsymptoticConstant α) := by
  rw [chapter12UnconditionalLimitingLogExpression,
    chapter12UnconditionalAsymptoticConstant,
    chapter09UnconditionalAsymptoticConstant]
  have hlogprod :
      Real.log (4 * Real.pi * Real.exp
        (chapter09EulerMascheroni + α)) =
        Real.log (4 * Real.pi) +
          (chapter09EulerMascheroni + α) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hlog8 :
      Real.log (8 * Real.pi) - Real.log 2 =
        Real.log (4 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = (4 * Real.pi) * 2 by ring,
      Real.log_mul (by positivity) (by positivity)]
    ring
  calc
    Real.eulerMascheroniConstant + Real.log (8 * Real.pi) - Real.log 2 + α =
        Real.eulerMascheroniConstant +
          (Real.log (8 * Real.pi) - Real.log 2) + α := by ring
    _ = Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + α := by
      rw [hlog8]
    _ = Real.log (4 * Real.pi) + (chapter09EulerMascheroni + α) := by ring
    _ = Real.log (4 * Real.pi * Real.exp
        (chapter09EulerMascheroni + α)) := hlogprod.symm

def chapter12UnconditionalArchimedeanDeficit (T α : ℝ) : ℝ :=
  chapter12UnconditionalLimitingLogExpression α -
    chapter12UnconditionalInfiniteDegreeLogExpression T α

/- LOCAL_DEPENDENCY_GUESS: these are the analytic limits proved upstream by
   the exact archimedean formulas.  They are stated here as a bridge because
   the current Chapter 11 dependency file exposes B and C but not their
   limiting theorems. -/
theorem chapter12_unconditional_B_tendsto :
    Tendsto chapter11B atTop (𝓝 (Real.log 2)) := by
  have hEq : chapter11B = chapter09BT := by
    funext T
    rw [chapter11_B_eq_chapter10_BT,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_BT_eq_chapter09_BT]
  rw [hEq]
  exact chapter09_unconditional_archimedean_B_tendsto

theorem chapter12_unconditional_C_tendsto :
    Tendsto chapter11C atTop (𝓝 (Real.pi / 2 - 1)) := by
  have hEq : chapter11C = chapter09CT := by
    funext T
    rw [chapter11_C_eq_chapter10_CT,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_CT_eq_chapter09_CT]
  rw [hEq]
  exact chapter09_unconditional_archimedean_C_tendsto

theorem chapter12_unconditional_archimedean_deficit_tendsto_zero
    (α : ℝ) :
    Tendsto (fun T : ℝ => chapter12UnconditionalArchimedeanDeficit T α)
      atTop (𝓝 0) := by
  have hB := chapter12_unconditional_B_tendsto
  have hC := chapter12_unconditional_C_tendsto
  have hbase : Tendsto
      (fun T : ℝ =>
        (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
          α * (Real.pi / 2)) - chapter11B T)
      atTop
      (𝓝 ((Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        α * (Real.pi / 2)) - Real.log 2)) := by
    simpa using (tendsto_const_nhds.sub hB)
  have hscaled : Tendsto (fun T : ℝ => α * chapter11C T)
      atTop (𝓝 (α * (Real.pi / 2 - 1))) := by
    simpa [mul_comm] using hC.const_mul α
  have hInf :
      Tendsto (fun T : ℝ => chapter12UnconditionalInfiniteDegreeLogExpression T α)
        atTop (𝓝 (chapter12UnconditionalLimitingLogExpression α)) := by
    have h := hbase.sub hscaled
    convert h using 1
    · simp only [chapter12UnconditionalInfiniteDegreeLogExpression]
    · simp only [chapter12UnconditionalLimitingLogExpression]
      ring_nf
  have hdef :
      Tendsto
        (fun T : ℝ =>
          chapter12UnconditionalLimitingLogExpression α -
            chapter12UnconditionalInfiniteDegreeLogExpression T α)
        atTop
        (𝓝 (chapter12UnconditionalLimitingLogExpression α -
          chapter12UnconditionalLimitingLogExpression α)) :=
    tendsto_const_nhds.sub hInf
  simpa [chapter12UnconditionalArchimedeanDeficit] using hdef

theorem chapter12_unconditional_archimedean_deficit_inverse_linear
    (α : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 < T₀ ∧
      ∀ T, T₀ ≤ T →
        |chapter12UnconditionalArchimedeanDeficit T α| ≤ C / T := by
  let q : ℝ := Real.exp (-1)
  let d : ℝ := 1 - q
  let d₂ : ℝ := 1 - Real.exp (-2)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hdpos : 0 < d := by
    dsimp [d, q]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    norm_num
  have hd₂pos : 0 < d₂ := by
    dsimp [d₂]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    norm_num
  let CB : ℝ := Real.pi ^ 2 / 4 + q * (1 + d⁻¹) +
      2 * (2 + 2 * d₂⁻¹)
  refine ⟨CB + |α| * (2 * Real.log 2), 1, ?_, by norm_num, ?_⟩
  · have hd_inv : 0 ≤ d⁻¹ := inv_nonneg.mpr hdpos.le
    have hd₂_inv : 0 ≤ d₂⁻¹ := inv_nonneg.mpr hd₂pos.le
    dsimp [CB]
    have hpi : 0 ≤ Real.pi ^ 2 / 4 := by positivity
    have hlog2 : 0 ≤ Real.log 2 := by
      apply Real.log_nonneg
      norm_num
    positivity
  · intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hBformula : chapter11B T =
        Real.log 2 + Real.pi ^ 2 / (4 * T) +
          Real.log (Chapter08.chapter08Coth (T / 2)) -
            (2 / T) *
              (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
      calc
        chapter11B T =
            LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10BT T :=
          chapter11_B_eq_chapter10_BT T
        _ = chapter09BT T :=
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_BT_eq_chapter09_BT T
        _ = Real.log 2 + Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2)) -
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
          simpa [chapter09BT, chapter09B, chapter09UnconditionalTestFunction,
            chapter09TriangularAutocorrelation, Chapter08.chapter08BT,
            Chapter08.chapter08B, Chapter08.chapter08FUnconditionalTriangle,
            Chapter08.chapter08TriangularAutocorrelation] using
            (Chapter08.chapter08_B_exact_formula hTpos)
    have hCformula : chapter11C T =
        Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
      calc
        chapter11C T =
            LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10CT T :=
          chapter11_C_eq_chapter10_CT T
        _ = chapter09CT T :=
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_CT_eq_chapter09_CT T
        _ = Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
          simpa [chapter09CT, chapter09C, chapter09UnconditionalTestFunction,
            chapter09TriangularAutocorrelation, Chapter08.chapter08CT,
            Chapter08.chapter08C, Chapter08.chapter08FUnconditionalTriangle,
            Chapter08.chapter08TriangularAutocorrelation] using
            (Chapter08.chapter08_C_exact_formula hTpos)
    have hloglower : T / 2 - Real.log 2 ≤
        Real.log (Real.cosh (T / 2)) := by
      have hcosh_lower : Real.exp (T / 2) / 2 ≤ Real.cosh (T / 2) := by
        rw [Real.cosh_eq]
        apply (div_le_div_iff_of_pos_right
          (by norm_num : (0 : ℝ) < 2)).2
        exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))
      have h := Real.log_le_log (by positivity :
        (0 : ℝ) < Real.exp (T / 2) / 2) hcosh_lower
      rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at h
      simpa [sub_eq_add_neg] using h
    have hlogupper : Real.log (Real.cosh (T / 2)) ≤ T / 2 := by
      have hcosh_upper : Real.cosh (T / 2) ≤ Real.exp (T / 2) := by
        rw [Real.cosh_eq]
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        have hneg : Real.exp (-(T / 2)) ≤ Real.exp (T / 2) :=
          Real.exp_le_exp.mpr (by linarith)
        linarith
      have h := Real.log_le_log (Real.cosh_pos _) hcosh_upper
      simpa using h
    have hCerr :
        |chapter11C T - (Real.pi / 2 - 1)| ≤
          2 * Real.log 2 / T := by
      rw [hCformula]
      have hrewrite :
          Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) -
              (Real.pi / 2 - 1) =
            1 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
        ring
      rw [hrewrite, abs_of_nonneg]
      · have hmulower :
            1 - 2 * Real.log 2 / T ≤
              (2 / T) * Real.log (Real.cosh (T / 2)) := by
          have hmul := mul_le_mul_of_nonneg_left hloglower
            (by positivity : 0 ≤ (2 / T : ℝ))
          calc
            1 - 2 * Real.log 2 / T =
                (2 / T) * (T / 2 - Real.log 2) := by
                  field_simp [ne_of_gt hTpos]
            _ ≤ (2 / T) * Real.log (Real.cosh (T / 2)) := hmul
        have hmulupper :
            (2 / T) * Real.log (Real.cosh (T / 2)) ≤ 1 := by
          have hmul := mul_le_mul_of_nonneg_left hlogupper
            (by positivity : 0 ≤ (2 / T : ℝ))
          calc
            (2 / T) * Real.log (Real.cosh (T / 2)) ≤
                (2 / T) * (T / 2) := hmul
            _ = 1 := by
              field_simp [ne_of_gt hTpos]
        linarith
      · have hmulupper :
            (2 / T) * Real.log (Real.cosh (T / 2)) ≤ 1 := by
          have hmul := mul_le_mul_of_nonneg_left hlogupper
            (by positivity : 0 ≤ (2 / T : ℝ))
          calc
            (2 / T) * Real.log (Real.cosh (T / 2)) ≤
                (2 / T) * (T / 2) := hmul
            _ = 1 := by
              field_simp [ne_of_gt hTpos]
        linarith
    have hsplit : Chapter08.chapter08BSeriesTerm T 0 +
          Chapter08.chapter08BSeriesTail T 0 =
            ∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k := by
      have h := (Chapter08.chapter08_B_series_summable (T := T) hTpos).sum_add_tsum_nat_add 1
      simpa [Chapter08.chapter08BSeriesTail, Nat.add_comm] using h
    have hterm0 : Chapter08.chapter08BSeriesTerm T 0 =
        (1 + T) * Real.exp (-T) := by
      simp [Chapter08.chapter08BSeriesTerm, Chapter08.chapter08Odd]
    have hterm0_nonneg : 0 ≤ Chapter08.chapter08BSeriesTerm T 0 := by
      rw [hterm0]
      positivity
    have htail_nonneg : 0 ≤ Chapter08.chapter08BSeriesTail T 0 :=
      Chapter08.chapter08_B_series_tail_nonnegative hTpos 0
    have hsum_nonneg : 0 ≤
        ∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k := by
      rw [← hsplit]
      exact add_nonneg hterm0_nonneg htail_nonneg
    have hTexp : T * Real.exp (-T) ≤ q := by
      simpa [q] using (Real.mul_exp_neg_le_exp_neg_one T)
    have hqone : q ≤ 1 := by
      dsimp [q]
      exact Real.exp_le_one_iff.mpr (by norm_num)
    have hTexpone : Real.exp (-T) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hfirst : (1 + T) * Real.exp (-T) ≤ 2 := by
      calc
        (1 + T) * Real.exp (-T) =
            Real.exp (-T) + T * Real.exp (-T) := by ring
        _ ≤ 1 + q := add_le_add hTexpone hTexp
        _ ≤ 2 := by linarith
    have hthreeexp : Real.exp (-3 * T) ≤ Real.exp (-T) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hthird : (1 + T) * Real.exp (-3 * T) ≤ 2 := by
      calc
        (1 + T) * Real.exp (-3 * T) ≤
            (1 + T) * Real.exp (-T) := by
              exact mul_le_mul_of_nonneg_left hthreeexp (by positivity)
        _ ≤ 2 := hfirst
    have hden₂ : d₂ ≤ 1 - Real.exp (-2 * T) := by
      dsimp [d₂]
      have h := Real.exp_le_exp.mpr (by linarith : -2 * T ≤ -(2 : ℝ))
      linarith
    have hden₂Tpos : 0 < 1 - Real.exp (-2 * T) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      linarith
    have htail : Chapter08.chapter08BSeriesTail T 0 ≤
        (1 + T) * Real.exp (-3 * T) /
          (1 - Real.exp (-2 * T)) := by
      simpa using (Chapter08.chapter08_B_series_tail_bound hTpos 0)
    have htail_div :
        (1 + T) * Real.exp (-3 * T) /
            (1 - Real.exp (-2 * T)) ≤ 2 / d₂ := by
      calc
        (1 + T) * Real.exp (-3 * T) /
            (1 - Real.exp (-2 * T)) ≤
              2 / (1 - Real.exp (-2 * T)) :=
          div_le_div_of_nonneg_right hthird hden₂Tpos.le
        _ ≤ 2 / d₂ :=
          div_le_div_of_nonneg_left (by norm_num) hd₂pos hden₂
    have hsum_upper :
        (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) ≤
          2 + 2 / d₂ := by
      rw [← hsplit]
      rw [hterm0]
      exact (add_le_add le_rfl (htail.trans htail_div)).trans
        (by linarith [hfirst])
    have hxd : d ≤ 1 - Real.exp (-T) := by
      dsimp [d, q]
      have h := Real.exp_le_exp.mpr (by linarith : -T ≤ -(1 : ℝ))
      linarith
    have hdenpos : 0 < 1 - Real.exp (-T) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      linarith
    have hlogcoth :
        Real.log (Chapter08.chapter08Coth (T / 2)) =
          Real.log (1 + Real.exp (-T)) -
            Real.log (1 - Real.exp (-T)) := by
      rw [← LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_coth_eq_chapter08_coth]
      exact LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter10.chapter10_log_coth_rewrite hTpos
    have hlogplus : Real.log (1 + Real.exp (-T)) ≤ Real.exp (-T) := by
      have h := Real.log_le_sub_one_of_pos (by positivity :
        (0 : ℝ) < 1 + Real.exp (-T))
      linarith
    have hlogminus :
        -Real.log (1 - Real.exp (-T)) ≤
          Real.exp (-T) / (1 - Real.exp (-T)) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hdenpos)
      calc
        -Real.log (1 - Real.exp (-T)) =
            Real.log (1 - Real.exp (-T))⁻¹ := by
              rw [Real.log_inv]
        _ ≤ (1 - Real.exp (-T))⁻¹ - 1 := h
        _ = Real.exp (-T) / (1 - Real.exp (-T)) := by
              field_simp [ne_of_gt hdenpos]
              ring
    have hdenbound :
        Real.exp (-T) / (1 - Real.exp (-T)) ≤ Real.exp (-T) / d :=
      div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hdpos hxd
    have hxoverT : Real.exp (-T) ≤ q / T := by
      apply (le_div_iff₀ hTpos).2
      simpa [mul_comm] using hTexp
    have hfactor :
        Real.exp (-T) + Real.exp (-T) / d =
          Real.exp (-T) * (1 + d⁻¹) := by
      field_simp [ne_of_gt hdpos]
    have hlogcoth_bound :
        Real.log (Chapter08.chapter08Coth (T / 2)) ≤
          q * (1 + d⁻¹) / T := by
      rw [hlogcoth]
      have hsumlog :
          Real.log (1 + Real.exp (-T)) - Real.log (1 - Real.exp (-T)) ≤
            Real.exp (-T) + Real.exp (-T) / (1 - Real.exp (-T)) := by
        linarith
      have hfacnonneg : 0 ≤ 1 + d⁻¹ := by positivity
      calc
        Real.log (1 + Real.exp (-T)) - Real.log (1 - Real.exp (-T)) ≤
            Real.exp (-T) + Real.exp (-T) / (1 - Real.exp (-T)) := hsumlog
        _ ≤ Real.exp (-T) + Real.exp (-T) / d := by linarith
        _ = Real.exp (-T) * (1 + d⁻¹) := hfactor
        _ ≤ (q / T) * (1 + d⁻¹) :=
          mul_le_mul_of_nonneg_right hxoverT hfacnonneg
        _ = q * (1 + d⁻¹) / T := by ring
    have hcoth_one : 1 ≤ Chapter08.chapter08Coth (T / 2) := by
      have hsinh : 0 < Real.sinh (T / 2) := by
        rw [Real.sinh_pos_iff]
        linarith
      unfold Chapter08.chapter08Coth
      apply (le_div_iff₀ hsinh).2
      rw [Real.cosh_eq, Real.sinh_eq]
      linarith [Real.exp_pos (-(T / 2))]
    have hlogcoth_nonneg : 0 ≤
        Real.log (Chapter08.chapter08Coth (T / 2)) :=
      Real.log_nonneg hcoth_one
    have hBdiff : chapter11B T - Real.log 2 =
        Real.pi ^ 2 / (4 * T) +
          Real.log (Chapter08.chapter08Coth (T / 2)) -
            (2 / T) *
              (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
      rw [hBformula]
      ring
    have hDnonneg : 0 ≤ (2 / T) *
        (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) :=
      mul_nonneg (by positivity) hsum_nonneg
    have hBerr : |chapter11B T - Real.log 2| ≤ CB / T := by
      rw [hBdiff]
      have hA_nonneg : 0 ≤ Real.pi ^ 2 / (4 * T) := by positivity
      have hAL_nonneg : 0 ≤ Real.pi ^ 2 / (4 * T) +
          Real.log (Chapter08.chapter08Coth (T / 2)) :=
        add_nonneg hA_nonneg hlogcoth_nonneg
      have hD : (2 / T) *
          (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) ≤
            2 * (2 + 2 / d₂) / T := by
        have hmul := mul_le_mul_of_nonneg_left hsum_upper
          (by positivity : 0 ≤ (2 / T : ℝ))
        calc
          (2 / T) *
              (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) ≤
              (2 / T) * (2 + 2 / d₂) := hmul
          _ = 2 * (2 + 2 / d₂) / T := by ring
      have habs :
          |Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2)) -
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k)| ≤
            (Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2))) +
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
        calc
          |Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2)) -
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k)| ≤
              |Real.pi ^ 2 / (4 * T) +
                Real.log (Chapter08.chapter08Coth (T / 2))| +
                |(2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k)| :=
            abs_sub _ _
          _ = (Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2))) +
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
            rw [abs_of_nonneg hAL_nonneg, abs_of_nonneg hDnonneg]
      have hAL : Real.pi ^ 2 / (4 * T) +
          Real.log (Chapter08.chapter08Coth (T / 2)) ≤
            (Real.pi ^ 2 / 4 + q * (1 + d⁻¹)) / T := by
        calc
          Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2)) ≤
              Real.pi ^ 2 / (4 * T) + q * (1 + d⁻¹) / T :=
            add_le_add le_rfl hlogcoth_bound
          _ = (Real.pi ^ 2 / 4 + q * (1 + d⁻¹)) / T := by ring
      calc
        |Real.pi ^ 2 / (4 * T) +
            Real.log (Chapter08.chapter08Coth (T / 2)) -
              (2 / T) *
                (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k)| ≤
            (Real.pi ^ 2 / (4 * T) +
              Real.log (Chapter08.chapter08Coth (T / 2))) +
                (2 / T) *
                  (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := habs
        _ ≤ (Real.pi ^ 2 / 4 + q * (1 + d⁻¹)) / T +
              2 * (2 + 2 / d₂) / T := add_le_add hAL hD
        _ = CB / T := by
          dsimp [CB]
          ring
    have hdecomp : chapter12UnconditionalArchimedeanDeficit T α =
        (chapter11B T - Real.log 2) +
          α * (chapter11C T - (Real.pi / 2 - 1)) := by
      simp [chapter12UnconditionalArchimedeanDeficit,
        chapter12UnconditionalLimitingLogExpression,
        chapter12UnconditionalInfiniteDegreeLogExpression]
      ring
    rw [hdecomp]
    have hαC : |α| *
          |chapter11C T - (Real.pi / 2 - 1)| ≤
        |α| * (2 * Real.log 2 / T) :=
      mul_le_mul_of_nonneg_left hCerr (abs_nonneg α)
    have htotal :
        |chapter11B T - Real.log 2| +
            |α| * |chapter11C T - (Real.pi / 2 - 1)| ≤
          CB / T + |α| * (2 * Real.log 2 / T) :=
      add_le_add hBerr hαC
    calc
      |(chapter11B T - Real.log 2) +
          α * (chapter11C T - (Real.pi / 2 - 1))| ≤
          |chapter11B T - Real.log 2| +
            |α| * |chapter11C T - (Real.pi / 2 - 1)| := by
        calc
          |(chapter11B T - Real.log 2) +
              α * (chapter11C T - (Real.pi / 2 - 1))| ≤
              |chapter11B T - Real.log 2| +
              |α * (chapter11C T - (Real.pi / 2 - 1))| := abs_add_le _ _
          _ = |chapter11B T - Real.log 2| +
              |α| * |chapter11C T - (Real.pi / 2 - 1)| := by
            rw [abs_mul]
      _ ≤ CB / T + |α| * (2 * Real.log 2 / T) := htotal
      _ = (CB + |α| * (2 * Real.log 2)) / T := by
        field_simp [ne_of_gt hTpos]

def chapter12CrudeFiniteDegreeScale (n : ℕ) (T : ℝ) : ℝ :=
  2 * T / (n : ℝ)

def chapter12CrudeArchimedeanScale (T : ℝ) : ℝ :=
  1 / T

def chapter12CrudeBalanceScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / 2)

theorem chapter12_crude_balance_scale_eq
    {n : ℕ} (hn : 0 < n) :
    chapter12CrudeFiniteDegreeScale n (chapter12CrudeBalanceScale n) =
      chapter12CrudeArchimedeanScale (chapter12CrudeBalanceScale n) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsarg : 0 ≤ (n : ℝ) / 2 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) / 2) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hsquare : (Real.sqrt ((n : ℝ) / 2)) ^ 2 = (n : ℝ) / 2 :=
    Real.sq_sqrt hsarg
  unfold chapter12CrudeFiniteDegreeScale chapter12CrudeArchimedeanScale
    chapter12CrudeBalanceScale
  field_simp [ne_of_gt hn', ne_of_gt hs]
  nlinarith [hsquare]

def chapter12GRHPoleCost (n : ℕ) (T : ℝ) : ℝ :=
  4 * chapter09GRHPoleIntegral T / (n : ℝ)

def chapter12GRHExponentialPoleScale (n : ℕ) (T : ℝ) : ℝ :=
  Real.exp (T / 2) / ((n : ℝ) * T)

def chapter12GRHArchimedeanLoss (T α : ℝ) : ℝ :=
  chapter09GRHBT T + α * chapter09GRHCT T

theorem chapter12_grh_pole_integral_exact
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHPoleIntegral T = 4 / T * (Real.cosh (T / 2) - 1) := by
  exact chapter09_grh_pole_integral hT

theorem chapter12_unconditional_pole_integral_exact
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalPoleIntegral T = T / 2 := by
  exact chapter09_unconditional_pole_integral hT

theorem chapter12_grh_pole_cost_has_exponential_over_nT_scale
    :
    ∃ c₁ c₂ T₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < T₀ ∧
      ∀ n, 0 < n → ∀ T, T₀ ≤ T →
        c₁ * chapter12GRHExponentialPoleScale n T ≤
            chapter12GRHPoleCost n T ∧
          chapter12GRHPoleCost n T ≤
            c₂ * chapter12GRHExponentialPoleScale n T := by
  refine ⟨8 * (1 - Real.exp (-(1 : ℝ) / 2)) ^ 2, 8, 1, ?_, by norm_num,
    by norm_num, ?_⟩
  · have hpos : 0 < 1 - Real.exp (-(1 : ℝ) / 2) := by
      apply sub_pos.mpr
      rw [Real.exp_lt_one_iff]
      norm_num
    nlinarith [sq_pos_of_pos hpos]
  · intro n hn T hT0
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT0
    have hcosh :
        Real.cosh (T / 2) - 1 =
          Real.exp (T / 2) / 2 * (1 - Real.exp (-(T / 2))) ^ 2 := by
      rw [Real.cosh_eq]
      field_simp [Real.exp_ne_zero]
      ring_nf
      have hprod :
          Real.exp (T * (1 / 2)) * Real.exp (T * (-1 / 2)) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring_nf
      rw [show Real.exp (T * (1 / 2)) * Real.exp (T * (-1 / 2)) ^ 2 =
        (Real.exp (T * (1 / 2)) * Real.exp (T * (-1 / 2))) *
          Real.exp (T * (-1 / 2)) by ring, hprod]
      ring
    have hcost :
        chapter12GRHPoleCost n T =
          8 * chapter12GRHExponentialPoleScale n T *
            (1 - Real.exp (-(T / 2))) ^ 2 := by
      rw [chapter12GRHPoleCost, chapter12_grh_pole_integral_exact hT,
        chapter12GRHExponentialPoleScale, hcosh]
      field_simp [ne_of_gt hn', ne_of_gt hT, Real.exp_ne_zero]
      ring
    have hu0 : 0 ≤ 1 - Real.exp (-(T / 2)) := by
      apply sub_nonneg.mpr
      have h := Real.exp_le_exp.mpr (show -(T / 2) ≤ 0 by linarith)
      simpa using h
    have hu1 : 1 - Real.exp (-(T / 2)) ≤ 1 := by
      linarith [Real.exp_nonneg (-(T / 2))]
    have husq : (1 - Real.exp (-(T / 2))) ^ 2 ≤ 1 := by
      nlinarith
    have hscale_pos : 0 < chapter12GRHExponentialPoleScale n T := by
      unfold chapter12GRHExponentialPoleScale
      positivity
    have hupper : chapter12GRHPoleCost n T ≤
        8 * chapter12GRHExponentialPoleScale n T := by
      rw [hcost]
      nlinarith [husq, hscale_pos]
    have hdec : Real.exp (-(T / 2)) ≤ Real.exp (-(1 : ℝ) / 2) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hu_lower : 1 - Real.exp (-(1 : ℝ) / 2) ≤
        1 - Real.exp (-(T / 2)) := by linarith
    have hu_const : 0 ≤ 1 - Real.exp (-(1 : ℝ) / 2) := by
      apply sub_nonneg.mpr
      have h := Real.exp_le_exp.mpr (show -(1 : ℝ) / 2 ≤ 0 by norm_num)
      simpa using h
    have hu_sq_lower : (1 - Real.exp (-(1 : ℝ) / 2)) ^ 2 ≤
        (1 - Real.exp (-(T / 2))) ^ 2 := by
      nlinarith [hu_lower, hu_const, hu0]
    have hlower :
        8 * (1 - Real.exp (-(1 : ℝ) / 2)) ^ 2 *
            chapter12GRHExponentialPoleScale n T ≤
          chapter12GRHPoleCost n T := by
      rw [hcost]
      nlinarith [hu_sq_lower, hscale_pos]
    exact ⟨hlower, hupper⟩

def chapter12ExponentialDecay (f : ℝ → ℝ) : Prop :=
  ∃ C ρ T₀ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ 0 < T₀ ∧
    ∀ T, T₀ ≤ T → |f T| ≤ C * Real.exp (-ρ * T)

def chapter12InverseLinearDecay (f : ℝ → ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 < T₀ ∧
    ∀ T, T₀ ≤ T → |f T| ≤ C / T

private theorem chapter12_grh_linear_exp_integrable :
    IntegrableOn (fun x : ℝ => x * Real.exp (-x / 2)) (Set.Ioi 1) := by
  let g : ℝ → ℝ := fun x => -(2 * x + 4) * Real.exp (-x / 2)
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ),
      HasDerivAt g (x * Real.exp (-x / 2)) x := by
    intro x hx
    have hpoly : HasDerivAt (fun y : ℝ => -(2 * y + 4)) (-2 : ℝ) x := by
      have h := ((hasDerivAt_const x (4 : ℝ)).add
        ((hasDerivAt_id x).const_mul (2 : ℝ))).neg
      have hfun : (fun y : ℝ => -(2 * y + 4)) =
          -((fun x : ℝ => 4) + fun y : ℝ => 2 * id y) := by
        funext y
        dsimp [id]
        ring
      have hder : (-2 : ℝ) = -(0 + 2 * 1) := by ring
      rw [hfun, hder]
      exact h
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y / 2))
        ((-1 / 2 : ℝ) * Real.exp (-x / 2)) x := by
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm,
        mul_assoc] using
        ((Real.hasDerivAt_exp (-(1 / 2 : ℝ) * x)).comp x
          ((hasDerivAt_id x).const_mul (-(1 / 2 : ℝ))))
    have h := hpoly.mul hexp
    change HasDerivAt (fun y : ℝ =>
      -(2 * y + 4) * Real.exp (-y / 2))
      (x * Real.exp (-x / 2)) x
    have hfun : (fun y : ℝ =>
        -(2 * y + 4) * Real.exp (-y / 2)) =
        (fun y : ℝ => -(2 * y + 4)) *
          (fun y : ℝ => Real.exp (-y / 2)) := by
      funext y
      rfl
    have hder : x * Real.exp (-x / 2) =
        -2 * Real.exp (-x / 2) +
          -(2 * x + 4) * ((-1 / 2 : ℝ) * Real.exp (-x / 2)) := by
      ring
    rw [hfun, hder]
    exact h
  have hpos : ∀ x ∈ Set.Ioi (1 : ℝ),
      0 ≤ x * Real.exp (-x / 2) := by
    intro x hx
    change 1 < x at hx
    exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  have hscale : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
      atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (f := fun x : ℝ => x) (l := atTop) (by norm_num : (0 : ℝ) < 1 / 2)).2
      Filter.tendsto_id
  have hpow :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hpow' : Tendsto (fun x : ℝ => (x / 2) * Real.exp (-x / 2))
      atTop (𝓝 0) := by
    change Tendsto (fun x : ℝ =>
      ((1 / 2 : ℝ) * x) ^ 1 * Real.exp (-((1 / 2 : ℝ) * x)))
      atTop (𝓝 0) at hpow
    have hpow'' : Tendsto
        (fun x : ℝ => (1 / 2 : ℝ) * x *
          Real.exp (-((1 / 2 : ℝ) * x))) atTop (𝓝 0) := by
      simpa only [pow_one] using hpow
    have hfun : (fun x : ℝ => (1 / 2 : ℝ) * x *
          Real.exp (-((1 / 2 : ℝ) * x))) =
        (fun x : ℝ => (x / 2) * Real.exp (-x / 2)) := by
      funext x
      congr 1
      · ring
      · congr 1
        ring
    rw [hfun] at hpow''
    exact hpow''
  have hexplim : Tendsto (fun x : ℝ => Real.exp (-x / 2))
      atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    change Tendsto (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x)))
      atTop (𝓝 0) at h
    have hfun : (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * x))) =
        (fun x : ℝ => Real.exp (-x / 2)) := by
      funext x
      congr 1
      ring
    rw [hfun] at h
    exact h
  have hpolyexplim : Tendsto
      (fun x : ℝ => (2 * x + 4) * Real.exp (-x / 2))
      atTop (𝓝 0) := by
    have h := (hpow'.const_mul (4 : ℝ)).add (hexplim.const_mul (4 : ℝ))
    have hfun : (fun x : ℝ => (2 * x + 4) * Real.exp (-x / 2)) =
        (fun x : ℝ => 4 * ((x / 2) * Real.exp (-x / 2)) +
          4 * Real.exp (-x / 2)) := by
      funext x
      ring
    rw [← hfun] at h
    simpa using h
  have hglim : Tendsto g atTop (𝓝 0) := by
    have hfun : g = (fun x : ℝ =>
        -((2 * x + 4) * Real.exp (-x / 2))) := by
      funext x
      dsimp [g]
      ring
    rw [hfun]
    simpa using hpolyexplim.neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hglim

private theorem chapter12_grh_weighted_sinh_integrable :
    IntegrableOn
      (fun x : ℝ => x / (2 * Real.sinh (x / 2))) (Set.Ioi 0) := by
  let d : ℝ := 1 - Real.exp (-1)
  have hdpos : 0 < d := by
    dsimp [d]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    norm_num
  have hsmall : IntegrableOn
      (fun x : ℝ => x / (2 * Real.sinh (x / 2))) (Set.Ioc 0 1) := by
    apply Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ))
      (s := Set.Ioc 0 1) (M := 1) (ne_of_lt measure_Ioc_lt_top)
    · exact (measurable_id.div
        (measurable_const.mul
          (Real.continuous_sinh.measurable.comp
            (measurable_id.div measurable_const)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hsinh : 0 < Real.sinh (x / 2) := by positivity
      have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hxpos hden)]
      apply (div_le_iff₀ hden).2
      have hsinh_lower : x / 2 ≤ Real.sinh (x / 2) :=
        Real.self_le_sinh_iff.mpr (by linarith)
      linarith
  have htail : IntegrableOn
      (fun x : ℝ => x / (2 * Real.sinh (x / 2))) (Set.Ioi 1) := by
    have hmajor : IntegrableOn
        (fun x : ℝ => d⁻¹ * (x * Real.exp (-x / 2))) (Set.Ioi 1) :=
      chapter12_grh_linear_exp_integrable.const_mul d⁻¹
    apply hmajor.mono'
    · exact (measurable_id.div
        (measurable_const.mul
          (Real.continuous_sinh.measurable.comp
            (measurable_id.div measurable_const)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change 1 < x at hx
      have hxpos : 0 < x := by linarith
      have hsinh : 0 < Real.sinh (x / 2) := by positivity
      have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
      have hdeneq : 2 * Real.sinh (x / 2) =
          Real.exp (x / 2) * (1 - Real.exp (-x)) := by
        rw [Real.sinh_eq]
        have hprod : Real.exp (x / 2) * Real.exp (-x) =
            Real.exp (-(x / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          2 * ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) =
              Real.exp (x / 2) - Real.exp (-(x / 2)) := by ring
          _ = Real.exp (x / 2) * (1 - Real.exp (-x)) := by
            rw [mul_sub, hprod]
            ring
      have hfactor : d ≤ 1 - Real.exp (-x) := by
        dsimp [d]
        have h := Real.exp_le_exp.mpr (by linarith : -x ≤ -(1 : ℝ))
        linarith
      have hdenlower : d * Real.exp (x / 2) ≤
          2 * Real.sinh (x / 2) := by
        calc
          d * Real.exp (x / 2) ≤
              (1 - Real.exp (-x)) * Real.exp (x / 2) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
          _ = Real.exp (x / 2) * (1 - Real.exp (-x)) := by ring
          _ = 2 * Real.sinh (x / 2) := hdeneq.symm
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hxpos hden)]
      calc
        x / (2 * Real.sinh (x / 2)) ≤
            x / (d * Real.exp (x / 2)) :=
          div_le_div_of_nonneg_left hxpos.le
            (mul_pos hdpos (Real.exp_pos _)) hdenlower
        _ = d⁻¹ * (x * Real.exp (-x / 2)) := by
          have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
            rw [← Real.exp_add]
            simp
          field_simp [ne_of_gt hdpos, Real.exp_ne_zero]
          rw [hprod]
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) (by norm_num)]
  exact hsmall.union htail

theorem chapter12_grh_archimedean_losses_tendsto_zero :
    Tendsto chapter09GRHBT atTop (𝓝 0) ∧
      Tendsto chapter09GRHCT atTop (𝓝 0) := by
  exact ⟨chapter09_grh_archimedean_B_tendsto,
    chapter09_grh_archimedean_C_tendsto⟩

theorem chapter12_grh_archimedean_loss_tendsto_zero
    (α : ℝ) :
    Tendsto (fun T : ℝ => chapter12GRHArchimedeanLoss T α)
      atTop (𝓝 0) := by
  have hB := chapter09_grh_archimedean_B_tendsto
  have hC0 := chapter09_grh_archimedean_C_tendsto
  have hC : Tendsto (fun T : ℝ => α * chapter09GRHCT T)
      atTop (𝓝 0) := by
    simpa using hC0.const_mul α
  have h := hB.add hC
  simpa [chapter12GRHArchimedeanLoss] using h

theorem chapter12_grh_B_has_standard_decay :
    chapter12ExponentialDecay chapter09GRHBT ∨
      chapter12InverseLinearDecay chapter09GRHBT := by
  right
  let C : ℝ := ∫ x in Set.Ioi (0 : ℝ),
    x / (2 * Real.sinh (x / 2))
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    exact div_nonneg hxpos.le (by positivity)
  refine ⟨C, 1, hCnonneg, by norm_num, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hG := Chapter08.chapter08_grh_triangle_admissible
    (T := T) hTpos
  have hBint : IntegrableOn
      (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
        (2 * Real.sinh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FGRHTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hG.1).2.1
  have hmajor : IntegrableOn
      (fun x : ℝ => (1 / T) * (x / (2 * Real.sinh (x / 2))))
        (Set.Ioi 0) :=
    chapter12_grh_weighted_sinh_integrable.const_mul (1 / T)
  have hbound : chapter09GRHBT T ≤ C / T := by
    unfold chapter09GRHBT chapter09B
    calc
      (∫ x in Set.Ioi (0 : ℝ),
          (1 - chapter09GRHTestFunction T x) /
            (2 * Real.sinh (x / 2))) ≤
          ∫ x in Set.Ioi (0 : ℝ),
            (1 / T) * (x / (2 * Real.sinh (x / 2))) := by
        apply integral_mono_ae hBint hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxpos : 0 < x := hx
        have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
        change (1 - max (1 - |x| / T) 0) /
            (2 * Real.sinh (x / 2)) ≤
          (1 / T) * (x / (2 * Real.sinh (x / 2)))
        have hnumle : 1 - max (1 - |x| / T) 0 ≤ x / T := by
          have hmax : 1 - |x| / T ≤ max (1 - |x| / T) 0 :=
            le_max_left _ _
          rw [abs_of_pos hxpos] at hmax ⊢
          linarith
        calc
          (1 - max (1 - |x| / T) 0) /
              (2 * Real.sinh (x / 2)) ≤
              (x / T) / (2 * Real.sinh (x / 2)) :=
            div_le_div_of_nonneg_right hnumle hden.le
          _ = (1 / T) * (x / (2 * Real.sinh (x / 2))) := by ring
      _ = C / T := by
        dsimp [C]
        rw [integral_const_mul]
        ring
  have hnonneg : 0 ≤ chapter09GRHBT T := by
    unfold chapter09GRHBT chapter09B
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
    change 0 ≤ (1 - max (1 - |x| / T) 0) /
      (2 * Real.sinh (x / 2))
    have hquot : 0 ≤ |x| / T := div_nonneg (abs_nonneg _) hTpos.le
    have hmax : max (1 - |x| / T) 0 ≤ 1 := by
      apply max_le
      · linarith
      · norm_num
    exact div_nonneg (sub_nonneg.mpr hmax) hden.le
  rw [abs_of_nonneg hnonneg]
  exact hbound

theorem chapter12_grh_C_has_standard_decay :
    chapter12ExponentialDecay chapter09GRHCT ∨
      chapter12InverseLinearDecay chapter09GRHCT := by
  right
  let C : ℝ := ∫ x in Set.Ioi (0 : ℝ),
    x / (2 * Real.sinh (x / 2))
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    exact div_nonneg hxpos.le (by positivity)
  refine ⟨C, 1, hCnonneg, by norm_num, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hG := Chapter08.chapter08_grh_triangle_admissible
    (T := T) hTpos
  have hCint : IntegrableOn
      (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
        (2 * Real.cosh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FGRHTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hG.1).2.2
  have hmajor : IntegrableOn
      (fun x : ℝ => (1 / T) * (x / (2 * Real.sinh (x / 2))))
        (Set.Ioi 0) :=
    chapter12_grh_weighted_sinh_integrable.const_mul (1 / T)
  have hbound : chapter09GRHCT T ≤ C / T := by
    unfold chapter09GRHCT chapter09C
    calc
      (∫ x in Set.Ioi (0 : ℝ),
          (1 - chapter09GRHTestFunction T x) /
            (2 * Real.cosh (x / 2))) ≤
          ∫ x in Set.Ioi (0 : ℝ),
            (1 / T) * (x / (2 * Real.sinh (x / 2))) := by
        apply integral_mono_ae hCint hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxpos : 0 < x := hx
        have hsinh : 0 < 2 * Real.sinh (x / 2) := by positivity
        have hcosh : 0 < 2 * Real.cosh (x / 2) := by positivity
        change (1 - max (1 - |x| / T) 0) /
            (2 * Real.cosh (x / 2)) ≤
          (1 / T) * (x / (2 * Real.sinh (x / 2)))
        have hquot : 0 ≤ |x| / T := div_nonneg (abs_nonneg _) hTpos.le
        have hmax : max (1 - |x| / T) 0 ≤ 1 := by
          apply max_le
          · linarith
          · norm_num
        have hnum_nonneg :
            0 ≤ 1 - max (1 - |x| / T) 0 := sub_nonneg.mpr hmax
        have hnumle : 1 - max (1 - |x| / T) 0 ≤ x / T := by
          have hmax' : 1 - |x| / T ≤ max (1 - |x| / T) 0 :=
            le_max_left _ _
          rw [abs_of_pos hxpos] at hmax' ⊢
          linarith
        have hdenle : 2 * Real.sinh (x / 2) ≤
            2 * Real.cosh (x / 2) := by
          rw [Real.sinh_eq, Real.cosh_eq]
          linarith [Real.exp_nonneg (-(x / 2))]
        calc
          (1 - max (1 - |x| / T) 0) /
              (2 * Real.cosh (x / 2)) ≤
              (1 - max (1 - |x| / T) 0) /
                (2 * Real.sinh (x / 2)) :=
            div_le_div_of_nonneg_left hnum_nonneg hsinh hdenle
          _ ≤ (x / T) / (2 * Real.sinh (x / 2)) :=
            div_le_div_of_nonneg_right hnumle hsinh.le
          _ = (1 / T) * (x / (2 * Real.sinh (x / 2))) := by ring
      _ = C / T := by
        dsimp [C]
        rw [integral_const_mul]
        ring
  have hnonneg : 0 ≤ chapter09GRHCT T := by
    unfold chapter09GRHCT chapter09C
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hden : 0 < 2 * Real.cosh (x / 2) := by positivity
    change 0 ≤ (1 - max (1 - |x| / T) 0) /
      (2 * Real.cosh (x / 2))
    have hquot : 0 ≤ |x| / T := div_nonneg (abs_nonneg _) hTpos.le
    have hmax : max (1 - |x| / T) 0 ≤ 1 := by
      apply max_le
      · linarith
      · norm_num
    exact div_nonneg (sub_nonneg.mpr hmax) hden.le
  rw [abs_of_nonneg hnonneg]
  exact hbound

def chapter12GRHLogarithmicSupportScale (n : ℕ) : ℝ :=
  if 1 < n then 2 * Real.log (n : ℝ) else 0

theorem chapter12_grh_useful_support_scale_is_logarithmic :
    Tendsto
      (fun n : ℕ =>
        if 1 < n then
          chapter12GRHLogarithmicSupportScale n / Real.log (n : ℝ)
        else 0)
      atTop (𝓝 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnne : (n : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hn)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnpos hnne
  simp [chapter12GRHLogarithmicSupportScale, hn, hlog]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
