import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Section04GammaAndPoleTerms
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section01TheThreeGoverningIntegrals
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section03ExactEvaluationOfTheArchimedeanTerms

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ## 9. Universal Odlyzko--Poitou inequalities -/

/-! ### 9.1 One test function, one rigorous bound -/

theorem chapter09_universal_odlyzko_poitou_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    Real.exp (chapter09UnconditionalExponent K T) ≤
      chapter09RootDiscriminant K := by
  sorry

theorem chapter09_universal_odlyzko_poitou_log_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalExponent K T ≤
      Real.log (chapter09RootDiscriminant K) := by
  have hbound := chapter09_universal_odlyzko_poitou_bound K hT
  rw [← Real.exp_le_exp]
  simpa [Real.exp_log (chapter09_root_discriminant_pos K)] using hbound

/-! ### 9.2 Unconditional asymptotic constants -/

theorem chapter09_unconditional_archimedean_B_tendsto :
    Tendsto chapter09BT atTop (𝓝 (Real.log 2)) := by
  have hsplit : ∀ {T : ℝ}, 0 < T →
      Chapter08.chapter08BSeriesTerm T 0 +
          Chapter08.chapter08BSeriesTail T 0 =
        ∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k := by
    intro T hT
    have h := (Chapter08.chapter08_B_series_summable (T := T) hT).sum_add_tsum_nat_add 1
    simpa [Chapter08.chapter08BSeriesTail, Nat.add_comm] using h
  have hdiv2 : Tendsto (fun x : ℝ => 2 / x) atTop (𝓝 0) := by
    exact Filter.Tendsto.const_div_atTop Filter.tendsto_id 2
  have hscale2 : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (f := fun x : ℝ => x) (l := Filter.atTop)
      (by norm_num : (0 : ℝ) < 2)).2 Filter.tendsto_id
  have hscale3 : Tendsto (fun x : ℝ => 3 * x) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (f := fun x : ℝ => x) (l := Filter.atTop)
      (by norm_num : (0 : ℝ) < 3)).2 Filter.tendsto_id
  have hdecay : Tendsto
      (fun x : ℝ => (1 + x) * Real.exp (-x)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x * Real.exp (-x))
        atTop (𝓝 0) := by
      simpa [pow_one] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.add hpow
    convert h using 1
    · funext x
      ring
    · simp
  have hdecay3 : Tendsto
      (fun x : ℝ => (1 + x) * Real.exp (-3 * x)) atTop (𝓝 0) := by
    have hpow :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale3
    have hpow' : Tendsto (fun x : ℝ => x * Real.exp (-3 * x))
        atTop (𝓝 0) := by
      have h := hpow.const_mul (1 / 3)
      convert h using 1
      · funext x
        simp only [Function.comp_apply, pow_one]
        ring_nf
      · simp
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale3
    have hexp' : Tendsto (fun x : ℝ => Real.exp (-3 * x))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using hexp
    have h := hexp'.add hpow'
    convert h using 1 <;> ring_nf
  have hden : Tendsto (fun x : ℝ => 1 - Real.exp (-2 * x))
      atTop (𝓝 1) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale2
    have hexp' : Tendsto (fun x : ℝ => Real.exp (-2 * x))
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using hexp
    simpa using (tendsto_const_nhds.sub hexp')
  have hden_inv : Tendsto
      (fun x : ℝ => (1 - Real.exp (-2 * x))⁻¹) atTop (𝓝 1) := by
    have h := (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hden
    simpa [Function.comp_def] using h
  have htail_decay : Tendsto
      (fun x : ℝ => (1 + x) * Real.exp (-3 * x) /
        (1 - Real.exp (-2 * x))) atTop (𝓝 0) := by
    have h := hdecay3.mul hden_inv
    simpa [div_eq_mul_inv] using h
  have hupper : Tendsto
      (fun x : ℝ => (2 / x) *
        ((1 + x) * Real.exp (-x) +
          (1 + x) * Real.exp (-3 * x) /
            (1 - Real.exp (-2 * x)))) atTop (𝓝 0) := by
    have h := hdiv2.mul (hdecay.add htail_decay)
    simpa using h
  have hseries_mul : Tendsto
      (fun T : ℝ => (2 / T) *
        (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hterm0 : 0 ≤ Chapter08.chapter08BSeriesTerm T 0 := by
        simp [Chapter08.chapter08BSeriesTerm, Chapter08.chapter08Odd]
        positivity
      have htail := Chapter08.chapter08_B_series_tail_nonnegative hT 0
      have hsum_nonneg : 0 ≤
          (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
        rw [← hsplit hT]
        exact add_nonneg hterm0 htail
      exact mul_nonneg (by positivity) hsum_nonneg
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hterm0 : Chapter08.chapter08BSeriesTerm T 0 =
          (1 + T) * Real.exp (-T) := by
        simp [Chapter08.chapter08BSeriesTerm, Chapter08.chapter08Odd]
      have htail : Chapter08.chapter08BSeriesTail T 0 ≤
          (1 + T) * Real.exp (-3 * T) /
            (1 - Real.exp (-2 * T)) := by
        simpa using (Chapter08.chapter08_B_series_tail_bound hT 0)
      have hsum : (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) ≤
          Chapter08.chapter08BSeriesTerm T 0 +
            ((1 + T) * Real.exp (-3 * T) /
              (1 - Real.exp (-2 * T))) := by
        rw [← hsplit hT]
        exact add_le_add le_rfl htail
      have hmul := mul_le_mul_of_nonneg_left hsum (by positivity :
        0 ≤ (2 / T : ℝ))
      calc
        (2 / T) * (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) ≤
            (2 / T) * (Chapter08.chapter08BSeriesTerm T 0 +
              ((1 + T) * Real.exp (-3 * T) /
                (1 - Real.exp (-2 * T)))) := hmul
        _ = (2 / T) *
            ((1 + T) * Real.exp (-T) +
              (1 + T) * Real.exp (-3 * T) /
                (1 - Real.exp (-2 * T))) := by rw [hterm0]
  have htan : Tendsto (fun x : ℝ => Real.tanh (x / 2))
      atTop (𝓝 1) := by
    have hscale : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
        atTop atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos
        (f := fun x : ℝ => x) (l := Filter.atTop)
        (by norm_num : (0 : ℝ) < 1 / 2)).2 Filter.tendsto_id
    have hexp_neg : Tendsto (fun x : ℝ => Real.exp (-x))
        atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
      have hnum : ContinuousAt (fun y : ℝ => 1 - y) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have hden' : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact hnum.div₀ hden' (by norm_num)
    have h := hcont.tendsto.comp hexp_neg
    have h' : Tendsto
        (fun x : ℝ => (1 - Real.exp (-x)) / (1 + Real.exp (-x)))
        atTop (𝓝 1) := by
      convert h using 1 <;> simp [Function.comp_def]
    have heq : ∀ x : ℝ, Real.tanh (x / 2) =
        (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
      intro x
      rw [Real.tanh_eq]
      have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      have ha : Real.exp (x / 2) = 1 / Real.exp (-(x / 2)) := by
        apply (eq_div_iff (Real.exp_ne_zero _)).2
        simpa using hprod
      have hsq : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hsq, ha]
      field_simp [Real.exp_ne_zero]
    simpa [heq] using h'
  have hlog_coth : Tendsto
      (fun x : ℝ => Real.log (Chapter08.chapter08Coth (x / 2)))
      atTop (𝓝 0) := by
    have hinv : Tendsto
        (fun x : ℝ => (Real.tanh (x / 2))⁻¹) atTop (𝓝 1) := by
      have h := (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp htan
      simpa [Function.comp_def] using h
    have hloginv : Tendsto
        (fun x : ℝ => Real.log ((Real.tanh (x / 2))⁻¹))
        atTop (𝓝 0) := by
      have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinv
      simpa [Function.comp_def, Real.log_one] using h
    have heq : ∀ᶠ x : ℝ in atTop,
        Chapter08.chapter08Coth (x / 2) = (Real.tanh (x / 2))⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      unfold Chapter08.chapter08Coth
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp [ne_of_gt (Real.cosh_pos (x / 2)), ne_of_gt
        (by rw [Real.sinh_pos_iff]; linarith : 0 < Real.sinh (x / 2))]
    exact hloginv.congr' (heq.mono fun x h => congrArg Real.log h.symm)
  have hpi : Tendsto (fun x : ℝ => (Real.pi ^ 2 / 4) / x)
      atTop (𝓝 0) := by
    exact Filter.Tendsto.const_div_atTop Filter.tendsto_id (Real.pi ^ 2 / 4)
  have hlimit : Tendsto
      (fun T : ℝ => Real.log 2 + (Real.pi ^ 2 / 4) / T +
        Real.log (Chapter08.chapter08Coth (T / 2)) -
          (2 / T) * (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k))
      atTop (𝓝 (Real.log 2)) := by
    have hconst : Tendsto (fun _ : ℝ => Real.log 2) atTop
        (𝓝 (Real.log 2)) := tendsto_const_nhds
    have h := hconst.add (hpi.add hlog_coth)
    have h' := h.sub hseries_mul
    simpa [add_assoc] using h'
  have hformula : ∀ᶠ T : ℝ in atTop,
      chapter09BT T = Real.log 2 + (Real.pi ^ 2 / 4) / T +
        Real.log (Chapter08.chapter08Coth (T / 2)) -
          (2 / T) * (∑' k : ℕ, Chapter08.chapter08BSeriesTerm T k) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := Chapter08.chapter08_B_exact_formula hT
    rw [show Real.pi ^ 2 / (4 * T) = (Real.pi ^ 2 / 4) / T by
      field_simp [ne_of_gt hT]] at h
    simpa [chapter09BT, chapter09B, chapter09UnconditionalTestFunction,
      chapter09TriangularAutocorrelation, Chapter08.chapter08BT,
      Chapter08.chapter08B, Chapter08.chapter08FUnconditionalTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using h
  exact hlimit.congr' (hformula.mono fun T h => h.symm)

theorem chapter09_unconditional_archimedean_C_tendsto :
    Tendsto chapter09CT atTop (𝓝 (Real.pi / 2 - 1)) := by
  have hsmall : Tendsto (fun T : ℝ => (2 * Real.log 2) / T)
      atTop (𝓝 0) := by
    exact Filter.Tendsto.const_div_atTop Filter.tendsto_id (2 * Real.log 2)
  have hlow : Tendsto (fun T : ℝ => 1 - (2 * Real.log 2) / T)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hsmall)
  have hquot : Tendsto
      (fun T : ℝ => (2 / T) * Real.log (Real.cosh (T / 2)))
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hcosh_lower : Real.exp (T / 2) / 2 ≤ Real.cosh (T / 2) := by
        rw [Real.cosh_eq]
        apply (div_le_div_iff_of_pos_right
          (by norm_num : (0 : ℝ) < 2)).2
        exact le_add_of_nonneg_right (le_of_lt (Real.exp_pos _))
      have hlog_lower : T / 2 - Real.log 2 ≤
          Real.log (Real.cosh (T / 2)) := by
        have h := Real.log_le_log (by positivity :
          (0 : ℝ) < Real.exp (T / 2) / 2) hcosh_lower
        rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at h
        simpa [sub_eq_add_neg] using h
      have hmul := mul_le_mul_of_nonneg_left hlog_lower
        (le_of_lt (by positivity : (0 : ℝ) < 2 / T))
      convert hmul using 1
      field_simp [ne_of_gt hT]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hcosh_upper : Real.cosh (T / 2) ≤ Real.exp (T / 2) := by
        rw [Real.cosh_eq]
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        have h := Real.exp_le_exp.mpr (by linarith : -(T / 2) ≤ T / 2)
        linarith
      have hlog_upper : Real.log (Real.cosh (T / 2)) ≤ T / 2 := by
        have h := Real.log_le_log (Real.cosh_pos _) hcosh_upper
        simpa using h
      have hmul := mul_le_mul_of_nonneg_left hlog_upper
        (le_of_lt (by positivity : (0 : ℝ) < 2 / T))
      convert hmul using 1
      field_simp [ne_of_gt hT]
  have hformula : ∀ᶠ T : ℝ in atTop,
      chapter09CT T = Real.pi / 2 -
        (2 / T) * Real.log (Real.cosh (T / 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa [chapter09CT, chapter09C, chapter09UnconditionalTestFunction,
      chapter09TriangularAutocorrelation, Chapter08.chapter08CT,
      Chapter08.chapter08C, Chapter08.chapter08FUnconditionalTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_C_exact_formula hT)
  have hlimit : Tendsto
      (fun T : ℝ => Real.pi / 2 -
        (2 / T) * Real.log (Real.cosh (T / 2)))
      atTop (𝓝 (Real.pi / 2 - 1)) := by
    simpa using (tendsto_const_nhds.sub hquot)
  exact hlimit.congr' (hformula.mono fun T h => h.symm)

def chapter09UnconditionalAsymptoticConstant (α₀ : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (chapter09EulerMascheroni + α₀)

theorem chapter09_unconditional_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf (chapter09SequenceRealProportion S) atTop)
    (hTdegree :
      Tendsto
        (fun j => T j / (chapter09SequenceDegree S j : ℝ))
        atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter09UnconditionalAsymptoticConstant α₀ := by
  sorry

theorem chapter09_unconditional_endpoint_constants :
    chapter09UnconditionalAsymptoticConstant 0 =
        4 * Real.pi * Real.exp chapter09EulerMascheroni ∧
      chapter09UnconditionalAsymptoticConstant 1 =
        4 * Real.pi * Real.exp (1 + chapter09EulerMascheroni) := by
  constructor <;> simp [chapter09UnconditionalAsymptoticConstant, add_comm]

/- The source prints decimal approximations with an ellipsis.  These rational
enclosures record the mathematical content without treating a decimal with
ellipsis as an equality. -/
theorem chapter09_unconditional_endpoint_zero_decimal_bounds :
    (223816160954 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09UnconditionalAsymptoticConstant 0 ∧
      chapter09UnconditionalAsymptoticConstant 0 <
        (223816160955 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

theorem chapter09_unconditional_endpoint_one_decimal_bounds :
    (608395403238 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09UnconditionalAsymptoticConstant 1 ∧
      chapter09UnconditionalAsymptoticConstant 1 <
        (608395403239 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

/-! ### 9.3 Bounds under the generalized Riemann hypothesis -/

theorem chapter09_grh_archimedean_B_tendsto :
    Tendsto chapter09GRHBT atTop (𝓝 0) := by
  let G : ℝ → ℝ := fun x =>
    if x ≤ 1 then 1 else 1 / (2 * Real.sinh (x / 2))
  have hG1 := Chapter08.chapter08_grh_triangle_admissible
    (T := (1 : ℝ)) (by norm_num)
  have hbase1 : IntegrableOn
      (fun x : ℝ => (1 - chapter09GRHTestFunction (1 : ℝ) x) /
        (2 * Real.sinh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FGRHTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hG1.1).2.1
  have hsmall : IntegrableOn G (Set.Ioc (0 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    apply hconst.congr_fun
    · intro x hx
      simp [G, hx.2]
    · exact measurableSet_Ioc
  have htail : IntegrableOn G (Set.Ioi (1 : ℝ)) := by
    have hraw := hbase1.mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    apply hraw.congr_fun
    · intro x hx
      change 1 < x at hx
      have hxpos : 0 < x := lt_trans (by norm_num) hx
      have hF : chapter09GRHTestFunction (1 : ℝ) x = 0 := by
        unfold chapter09GRHTestFunction chapter09TriangularAutocorrelation
        rw [abs_of_pos hxpos, show x / 1 = x by ring, max_eq_right]
        linarith
      dsimp [G]
      rw [if_neg (not_le_of_gt hx)]
      simp [hF]
    · exact measurableSet_Ioi
  have henv : IntegrableOn G (Set.Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) (by norm_num)]
    exact hsmall.union htail
  have hmeas : ∀ᶠ T : ℝ in atTop,
      AEStronglyMeasurable
        (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
          (2 * Real.sinh (x / 2))) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    change AEStronglyMeasurable
      (fun x : ℝ => (1 - max (1 - |x| / T) 0) /
        (2 * Real.sinh (x / 2))) (volume.restrict (Set.Ioi 0))
    have hnum : Continuous (fun x : ℝ => 1 - max (1 - |x| / T) 0) :=
      continuous_const.sub
        ((continuous_const.sub (continuous_abs.div_const T)).max
          continuous_const)
    exact (hnum.measurable.div
      (measurable_const.mul
        (Real.continuous_sinh.measurable.comp
          (measurable_id.div measurable_const)))).aestronglyMeasurable
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖(fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
          (2 * Real.sinh (x / 2))) x‖ ≤ G x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have htri0 : 0 ≤ chapter09TriangularAutocorrelation T x :=
      le_max_right _ _
    have htri1 : chapter09TriangularAutocorrelation T x ≤ 1 := by
      apply max_le
      · have hquot : 0 ≤ |x| / T :=
          div_nonneg (abs_nonneg _) (by linarith)
        linarith
      · norm_num
    have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
    have hnum : 0 ≤ 1 - chapter09GRHTestFunction T x := by
      simpa [chapter09GRHTestFunction] using sub_nonneg.mpr htri1
    have hF0 : 0 ≤ chapter09GRHTestFunction T x := by
      simpa [chapter09GRHTestFunction] using htri0
    have hnumleq : 1 - chapter09GRHTestFunction T x ≤ |x| / T := by
      simp only [chapter09GRHTestFunction, chapter09TriangularAutocorrelation]
      have hmax : 1 - |x| / T ≤ max (1 - |x| / T) 0 := le_max_left _ _
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le)]
    by_cases hxsmall : x ≤ 1
    · dsimp [G]
      rw [if_pos hxsmall]
      apply (div_le_iff₀ hden).2
      have hdenx : x ≤ 2 * Real.sinh (x / 2) := by
        have hsinh : x / 2 ≤ Real.sinh (x / 2) := by
          exact Real.self_le_sinh_iff.mpr (by linarith)
        linarith
      have hquot : |x| / T ≤ x := by
        rw [abs_of_pos hxpos]
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < T)).2
        nlinarith
      exact le_trans (le_trans hnumleq hquot) (by simpa using hdenx)
    · dsimp [G]
      rw [if_neg hxsmall]
      apply (div_le_iff₀ hden).2
      calc
        1 - chapter09GRHTestFunction T x ≤ 1 := by linarith
        _ = (1 / (2 * Real.sinh (x / 2))) *
            (2 * Real.sinh (x / 2)) := by field_simp [ne_of_gt hden]
  have hlim_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto
        (fun T : ℝ =>
          (1 - chapter09GRHTestFunction T x) /
            (2 * Real.sinh (x / 2))) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hdivx : Tendsto (fun T : ℝ => |x| / T) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop Filter.tendsto_id |x|
    have hlin : Tendsto (fun T : ℝ => 1 - |x| / T)
        atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdivx)
    have heq : ∀ᶠ T : ℝ in atTop,
        chapter09TriangularAutocorrelation T x = 1 - |x| / T := by
      filter_upwards [eventually_ge_atTop |x|, eventually_gt_atTop (0 : ℝ)]
        with T hTx hT
      rw [chapter09TriangularAutocorrelation, max_eq_left]
      have hquot : |x| / T ≤ 1 := (div_le_one hT).2 hTx
      linarith
    have htri : Tendsto (fun T : ℝ =>
        chapter09TriangularAutocorrelation T x) atTop (𝓝 1) :=
      hlin.congr' (heq.mono fun T h => h.symm)
    have hsub : Tendsto (fun T : ℝ =>
        1 - chapter09GRHTestFunction T x) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa [chapter09GRHTestFunction] using hconst.sub htri
    simpa [chapter09GRHTestFunction] using
      hsub.div_const (2 * Real.sinh (x / 2))
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun T x : ℝ =>
      (1 - chapter09GRHTestFunction T x) /
        (2 * Real.sinh (x / 2)))
    (f := fun _ : ℝ => (0 : ℝ)) G hmeas hbound henv hlim_ae
  change Tendsto (fun T : ℝ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - chapter09GRHTestFunction T x) /
        (2 * Real.sinh (x / 2))) atTop (𝓝 0)
  simpa using hDCT

theorem chapter09_grh_archimedean_C_tendsto :
    Tendsto chapter09GRHCT atTop (𝓝 0) := by
  have hU := Chapter08.chapter08_unconditional_triangle_admissible
    (T := (1 : ℝ)) (by norm_num)
  have hcont : Continuous (chapter09UnconditionalTestFunction (1 : ℝ)) := by
    change Continuous (Chapter08.chapter08FUnconditionalTriangle (1 : ℝ))
    exact hU.1.2.1
  have hcompact : HasCompactSupport
      (chapter09UnconditionalTestFunction (1 : ℝ)) := by
    change HasCompactSupport (Chapter08.chapter08FUnconditionalTriangle (1 : ℝ))
    exact hU.1.2.2.1
  have hdivcont : Continuous
      (fun x : ℝ => chapter09UnconditionalTestFunction (1 : ℝ) x /
        (2 * Real.cosh (x / 2))) := by
    have hhalf : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const _
    have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) :=
      continuous_const.mul (Real.continuous_cosh.comp hhalf)
    apply Continuous.div hcont hden
    intro x
    positivity
  have hdivcompact : HasCompactSupport
      (fun x : ℝ => chapter09UnconditionalTestFunction (1 : ℝ) x /
        (2 * Real.cosh (x / 2))) := by
    have hEq :
        (fun x : ℝ => chapter09UnconditionalTestFunction (1 : ℝ) x /
          (2 * Real.cosh (x / 2))) =
          chapter09UnconditionalTestFunction (1 : ℝ) *
            (fun x : ℝ => (2 * Real.cosh (x / 2))⁻¹) := by
      funext x
      simp only [Pi.mul_apply, div_eq_mul_inv]
    rw [hEq]
    exact hcompact.mul_right
  have hdiv : IntegrableOn
      (fun x : ℝ => chapter09UnconditionalTestFunction (1 : ℝ) x /
        (2 * Real.cosh (x / 2))) (Set.Ioi 0) :=
    (hdivcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ))
      hdivcompact).integrableOn
  have hC : IntegrableOn
      (fun x : ℝ => (1 - chapter09UnconditionalTestFunction (1 : ℝ) x) /
        (2 * Real.cosh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09UnconditionalTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FUnconditionalTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hU.1).2.2
  have hbase : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Set.Ioi 0) := by
    have hsum := hC.add hdiv
    convert hsum using 1
    · rfl
    · funext x
      have hden : 2 * Real.cosh (x / 2) ≠ 0 := by positivity
      simp only [Pi.add_apply]
      field_simp [hden]
      ring
  have hmeas : ∀ᶠ T : ℝ in atTop,
      AEStronglyMeasurable
        (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
          (2 * Real.cosh (x / 2))) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hcontT : Continuous
        (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
          (2 * Real.cosh (x / 2))) := by
      change Continuous (fun x : ℝ =>
        (1 - max (1 - |x| / T) 0) / (2 * Real.cosh (x / 2)))
      have hnum : Continuous (fun x : ℝ =>
          1 - max (1 - |x| / T) 0) :=
        continuous_const.sub
          ((continuous_const.sub (continuous_abs.div_const T)).max continuous_const)
      have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) :=
        continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const _))
      exact Continuous.div hnum hden (fun x => by positivity)
    exact hcontT.aestronglyMeasurable
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖(fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
          (2 * Real.cosh (x / 2))) x‖ ≤
        (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have htri0 : 0 ≤ chapter09TriangularAutocorrelation T x :=
      le_max_right _ _
    have htri1 : chapter09TriangularAutocorrelation T x ≤ 1 := by
      apply max_le
      · have hquot : 0 ≤ |x| / T :=
          div_nonneg (abs_nonneg _) (le_of_lt hT)
        linarith
      · norm_num
    have hden : 0 < 2 * Real.cosh (x / 2) := by positivity
    have hnum : 0 ≤ 1 - chapter09GRHTestFunction T x := by
      simpa [chapter09GRHTestFunction] using sub_nonneg.mpr htri1
    have hF0 : 0 ≤ chapter09GRHTestFunction T x := by
      simpa [chapter09GRHTestFunction] using htri0
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le)]
    apply (div_le_iff₀ hden).2
    calc
      1 - chapter09GRHTestFunction T x ≤ 1 := by linarith
      _ = (1 / (2 * Real.cosh (x / 2))) *
          (2 * Real.cosh (x / 2)) := by field_simp [ne_of_gt hden]
  have hlim_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto
        (fun T : ℝ =>
          (1 - chapter09GRHTestFunction T x) /
            (2 * Real.cosh (x / 2))) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hdivx : Tendsto (fun T : ℝ => |x| / T) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop Filter.tendsto_id |x|
    have hlin : Tendsto (fun T : ℝ => 1 - |x| / T)
        atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hdivx)
    have heq : ∀ᶠ T : ℝ in atTop,
        chapter09TriangularAutocorrelation T x = 1 - |x| / T := by
      filter_upwards [eventually_ge_atTop |x|, eventually_gt_atTop (0 : ℝ)]
        with T hTx hT
      rw [chapter09TriangularAutocorrelation, max_eq_left]
      have hquot : |x| / T ≤ 1 := (div_le_one hT).2 hTx
      linarith
    have htri : Tendsto (fun T : ℝ =>
        chapter09TriangularAutocorrelation T x) atTop (𝓝 1) :=
      hlin.congr' (heq.mono fun T h => h.symm)
    have hsub : Tendsto (fun T : ℝ =>
        1 - chapter09GRHTestFunction T x) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa [chapter09GRHTestFunction] using hconst.sub htri
    simpa [chapter09GRHTestFunction] using
      hsub.div_const (2 * Real.cosh (x / 2))
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi 0))
    (F := fun T x : ℝ =>
      (1 - chapter09GRHTestFunction T x) / (2 * Real.cosh (x / 2)))
    (f := fun _ : ℝ => (0 : ℝ))
    (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) hmeas hbound hbase hlim_ae
  change Tendsto (fun T : ℝ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - chapter09GRHTestFunction T x) /
        (2 * Real.cosh (x / 2))) atTop (𝓝 0)
  simpa using hDCT

/- The signature coefficient used by the threshold comparison is
   nonnegative for the two triangular test functions. -/
theorem chapter09_unconditional_archimedean_C_lt_pi_div_two
    {T : ℝ} (hT : 0 < T) :
    chapter09CT T < Real.pi / 2 := by
  have hformula := Chapter08.chapter08_C_exact_formula hT
  have hcosh : 1 < Real.cosh (T / 2) := by
    let a : ℝ := Real.exp (T / 2)
    let b : ℝ := Real.exp (-(T / 2))
    have ha : 1 < a := by
      dsimp [a]
      rw [Real.one_lt_exp_iff]
      linarith
    have hb : 0 < b := by
      dsimp [b]
      exact Real.exp_pos _
    have hab : a * b = 1 := by
      dsimp [a, b]
      rw [← Real.exp_add]
      ring_nf
      simp
    have hne : a - b ≠ 0 := by
      intro hab'
      have hab_eq : a = b := sub_eq_zero.mp hab'
      nlinarith
    have hsquare : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero hne
    rw [Real.cosh_eq]
    dsimp [a, b] at hab hsquare ⊢
    nlinarith
  have hlog : 0 < Real.log (Real.cosh (T / 2)) := Real.log_pos hcosh
  have hcost : 0 < (2 / T) * Real.log (Real.cosh (T / 2)) := by
    exact mul_pos (by positivity) hlog
  have hCT : chapter09CT T = Real.pi / 2 -
      (2 / T) * Real.log (Real.cosh (T / 2)) := by
    simpa [chapter09CT, chapter09C, chapter09UnconditionalTestFunction,
      chapter09TriangularAutocorrelation, Chapter08.chapter08CT,
      Chapter08.chapter08C, Chapter08.chapter08FUnconditionalTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using hformula
  rw [hCT]
  linarith

theorem chapter09_grh_archimedean_C_lt_pi_div_two
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHCT T < Real.pi / 2 := by
  have hU := Chapter08.chapter08_unconditional_triangle_admissible hT
  have hG := Chapter08.chapter08_grh_triangle_admissible hT
  have hU_C : IntegrableOn
      (fun x : ℝ => (1 - chapter09UnconditionalTestFunction T x) /
        (2 * Real.cosh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09UnconditionalTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FUnconditionalTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hU.1).2.2
  have hG_C : IntegrableOn
      (fun x : ℝ => (1 - chapter09GRHTestFunction T x) /
        (2 * Real.cosh (x / 2))) (Set.Ioi 0) := by
    simpa [chapter09GRHTestFunction, chapter09TriangularAutocorrelation,
      Chapter08.chapter08FGRHTriangle,
      Chapter08.chapter08TriangularAutocorrelation] using
      (Chapter08.chapter08_archimedean_integrals_convergent hG.1).2.2
  have hnonneg : 0 ≤ ∫ x in Set.Ioi (0 : ℝ),
      ((1 - chapter09UnconditionalTestFunction T x) /
          (2 * Real.cosh (x / 2))) -
        ((1 - chapter09GRHTestFunction T x) /
          (2 * Real.cosh (x / 2))) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have htri : 0 ≤ chapter09TriangularAutocorrelation T x := by
      exact le_max_right _ _
    have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
    have hcoshpos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
    dsimp [chapter09UnconditionalTestFunction, chapter09GRHTestFunction]
    field_simp [ne_of_gt hcoshpos]
    nlinarith
  have hsub := integral_sub hU_C hG_C
  have hCT : chapter09GRHCT T ≤ chapter09CT T := by
    unfold chapter09GRHCT chapter09CT chapter09C at *
    rw [hsub] at hnonneg
    linarith
  exact lt_of_le_of_lt hCT
    (chapter09_unconditional_archimedean_C_lt_pi_div_two hT)

theorem chapter09_grh_universal_odlyzko_poitou_bound
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    {T : ℝ} (hT : 0 < T) (hGRH : chapter09GRH K) :
    Real.exp (chapter09GRHExponent K T) ≤
      chapter09RootDiscriminant K := by
  sorry

def chapter09GRHAsymptoticConstant (α₀ : ℝ) : ℝ :=
  8 * Real.pi * Real.exp
    (chapter09EulerMascheroni + α₀ * (Real.pi / 2))

theorem chapter09_grh_asymptotic_lower_bound
    (S : Chapter09NumberFieldSequence) (α₀ : ℝ) (T : ℕ → ℝ)
    (hGRH : ∀ j, chapter09SequenceGRH S j)
    (hTpos : ∀ j, 0 < T j)
    (hT : Tendsto T atTop atTop)
    (hdegree : Tendsto (fun j => (chapter09SequenceDegree S j : ℝ)) atTop atTop)
    (halpha : α₀ ≤ Filter.liminf (chapter09SequenceRealProportion S) atTop)
    (hpole :
      Tendsto
        (fun j =>
          Real.exp (T j / 2) /
            ((chapter09SequenceDegree S j : ℝ) * T j))
        atTop (𝓝 0)) :
    Filter.liminf (chapter09SequenceRootDiscriminant S) atTop ≥
      chapter09GRHAsymptoticConstant α₀ := by
  sorry

theorem chapter09_grh_endpoint_constants :
    chapter09GRHAsymptoticConstant 0 =
        8 * Real.pi * Real.exp chapter09EulerMascheroni ∧
      chapter09GRHAsymptoticConstant 1 =
        8 * Real.pi * Real.exp
          (chapter09EulerMascheroni + Real.pi / 2) := by
  constructor <;> simp [chapter09GRHAsymptoticConstant]

theorem chapter09_grh_endpoint_zero_decimal_bounds :
    (447632321909 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09GRHAsymptoticConstant 0 ∧
      chapter09GRHAsymptoticConstant 0 <
        (447632321910 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

theorem chapter09_grh_endpoint_one_decimal_bounds :
    (2153325159534 : ℝ) / (10 : ℝ) ^ 10 <
        chapter09GRHAsymptoticConstant 1 ∧
      chapter09GRHAsymptoticConstant 1 <
        (2153325159535 : ℝ) / (10 : ℝ) ^ 10 := by
  sorry

/- A finite GRH certificate must retain a positive finite support parameter. -/
structure Chapter09FiniteGRHCertificate
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K] where
  T : ℝ
  T_pos : 0 < T
  grh : chapter09GRH K
  poleIntegral : ℝ
  B : ℝ
  C : ℝ
  poleIntegral_eq : poleIntegral = chapter09GRHPoleIntegral T
  B_eq : B = chapter09GRHBT T
  C_eq : C = chapter09GRHCT T

theorem chapter09_finite_grh_certificate_has_evaluated_test_function
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    (C : Chapter09FiniteGRHCertificate K) :
    0 < C.T ∧
      C.poleIntegral = chapter09GRHPoleIntegral C.T ∧
      C.B = chapter09GRHBT C.T ∧
      C.C = chapter09GRHCT C.T := by
  exact ⟨C.T_pos, C.poleIntegral_eq, C.B_eq, C.C_eq⟩

theorem chapter09_finite_grh_certificate_gives_bound
    (K : Type*) [Field K] [NumberField K]
    [Chapter09ZetaZeroInterface K]
    (C : Chapter09FiniteGRHCertificate K) :
    Real.exp
        (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
          chapter09RealProportion K * (Real.pi / 2) -
          4 * C.poleIntegral / (chapter09Degree K : ℝ) - C.B -
          chapter09RealProportion K * C.C) ≤
      chapter09RootDiscriminant K := by
  have h := chapter09_grh_universal_odlyzko_poitou_bound
    K C.T_pos C.grh
  simpa [chapter09GRHExponent, C.poleIntegral_eq, C.B_eq, C.C_eq] using h

/-! ### 9.4 Degree and signature monotonicity -/

def chapter09FixedTestFunctionConstant (F : Chapter09TestFunction) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) - chapter09B F

def chapter09FixedTestFunctionLogBound
    (F : Chapter09TestFunction) (n : ℕ) (α : ℝ) : ℝ :=
  chapter09FixedTestFunctionConstant F +
      α * (Real.pi / 2 - chapter09C F) -
    4 * chapter09A F / (n : ℝ)

def chapter09FixedLogCertificate
    (F : Chapter09TestFunction) (N : ℕ) (α₀ L : ℝ) : Prop :=
  L ≤ chapter09FixedTestFunctionLogBound F N α₀

theorem chapter09_unconditional_exponent_eq_fixed_test_function_log_bound
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalExponent K T =
      chapter09FixedTestFunctionLogBound
        (chapter09UnconditionalTestFunction T)
        (chapter09Degree K) (chapter09RealProportion K) := by
  have hA : chapter09A (chapter09UnconditionalTestFunction T) = T / 2 :=
    chapter09_unconditional_pole_integral hT
  unfold chapter09UnconditionalExponent chapter09FixedTestFunctionLogBound
    chapter09FixedTestFunctionConstant chapter09BT chapter09CT
  rw [hA]
  ring

theorem chapter09_fixed_log_bound_increases_with_degree
    (F : Chapter09TestFunction) {n m : ℕ} {α : ℝ}
    (hA : 0 ≤ chapter09A F) (hn : 0 < n) (hnm : n ≤ m) :
    chapter09FixedTestFunctionLogBound F n α ≤
      chapter09FixedTestFunctionLogBound F m α := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hdiv : chapter09A F / (m : ℝ) ≤ chapter09A F / (n : ℝ) := by
    exact div_le_div_of_nonneg_left hA hnR hnmR
  have hmul : (-4 : ℝ) * (chapter09A F / (n : ℝ)) ≤
      (-4 : ℝ) * (chapter09A F / (m : ℝ)) :=
    mul_le_mul_of_nonpos_left hdiv (by norm_num)
  unfold chapter09FixedTestFunctionLogBound
  calc
    chapter09FixedTestFunctionConstant F +
          α * (Real.pi / 2 - chapter09C F) -
        4 * chapter09A F / (n : ℝ) =
        chapter09FixedTestFunctionConstant F +
          α * (Real.pi / 2 - chapter09C F) +
            (-4 : ℝ) * (chapter09A F / (n : ℝ)) := by ring
    _ ≤ chapter09FixedTestFunctionConstant F +
          α * (Real.pi / 2 - chapter09C F) +
            (-4 : ℝ) * (chapter09A F / (m : ℝ)) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hmul
            (chapter09FixedTestFunctionConstant F +
              α * (Real.pi / 2 - chapter09C F)))
    _ = chapter09FixedTestFunctionConstant F +
          α * (Real.pi / 2 - chapter09C F) -
        4 * chapter09A F / (m : ℝ) := by ring

theorem chapter09_fixed_log_bound_increases_with_signature
    (F : Chapter09TestFunction) {n : ℕ} {α β : ℝ}
    (hαβ : α ≤ β) (hC : chapter09C F < Real.pi / 2) :
    chapter09FixedTestFunctionLogBound F n α ≤
      chapter09FixedTestFunctionLogBound F n β := by
  have hcoef : 0 ≤ Real.pi / 2 - chapter09C F := by linarith
  have hmul : α * (Real.pi / 2 - chapter09C F) ≤
      β * (Real.pi / 2 - chapter09C F) :=
    mul_le_mul_of_nonneg_right hαβ hcoef
  unfold chapter09FixedTestFunctionLogBound
  linarith

theorem chapter09_fixed_certificate_covers_larger_degree_and_signature
    (F : Chapter09TestFunction) {N n : ℕ} {α₀ α : ℝ}
    (hA : 0 ≤ chapter09A F) (hC : chapter09C F < Real.pi / 2)
    (hN : 0 < N) (hNn : N ≤ n) (hα : α₀ ≤ α) :
    chapter09FixedTestFunctionLogBound F N α₀ ≤
      chapter09FixedTestFunctionLogBound F n α := by
  calc
    chapter09FixedTestFunctionLogBound F N α₀ ≤
        chapter09FixedTestFunctionLogBound F n α₀ :=
      chapter09_fixed_log_bound_increases_with_degree F hA hN hNn
    _ ≤ chapter09FixedTestFunctionLogBound F n α :=
      chapter09_fixed_log_bound_increases_with_signature F hα hC

theorem chapter09_fixed_log_certificate_covers_larger_degree_and_signature
    (F : Chapter09TestFunction) {N n : ℕ} {α₀ α L : ℝ}
    (hcert : chapter09FixedLogCertificate F N α₀ L)
    (hA : 0 ≤ chapter09A F) (hC : chapter09C F < Real.pi / 2)
    (hN : 0 < N) (hNn : N ≤ n) (hα : α₀ ≤ α) :
    chapter09FixedLogCertificate F n α L := by
  exact le_trans hcert
    (chapter09_fixed_certificate_covers_larger_degree_and_signature
      F hA hC hN hNn hα)

/-! ### 9.5 Threshold and stabilization principles -/

def chapter09UnconditionalInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter09BT T - α₀ * chapter09CT T

def chapter09GRHInfiniteDegreeExponent
    (T α₀ : ℝ) : ℝ :=
  chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - chapter09GRHBT T - α₀ * chapter09GRHCT T

structure chapter09ThresholdCertificate (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter09UnconditionalInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    2 * (T : ℝ) / (N : ℝ) <
      chapter09UnconditionalInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

theorem chapter09_threshold_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter09UnconditionalAsymptoticConstant α₀) :
    Nonempty (chapter09ThresholdCertificate U α₀) := by
  have hconstpos : 0 < chapter09UnconditionalAsymptoticConstant α₀ := by
    unfold chapter09UnconditionalAsymptoticConstant
    positivity
  have hlogU : Real.log U <
      Real.log (chapter09UnconditionalAsymptoticConstant α₀) := by
    exact Real.strictMonoOn_log
      (show U ∈ Set.Ioi 0 from hUpos)
      (show chapter09UnconditionalAsymptoticConstant α₀ ∈ Set.Ioi 0 from hconstpos)
      hU
  have hlogconst :
      Real.log (chapter09UnconditionalAsymptoticConstant α₀) =
        chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2 := by
    calc
      Real.log (chapter09UnconditionalAsymptoticConstant α₀) =
          Real.log (4 * Real.pi) +
            Real.log (Real.exp (chapter09EulerMascheroni + α₀)) := by
        rw [chapter09UnconditionalAsymptoticConstant,
          Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (4 * Real.pi) + chapter09EulerMascheroni + α₀ := by
        rw [Real.log_exp]
        ring
      _ = chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2 := by
        rw [show (4 : ℝ) * Real.pi = (8 * Real.pi) / 2 by ring,
          Real.log_div (by positivity) (by norm_num)]
        ring
  have hlogU' : Real.log U <
      chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2 := by
    rw [← hlogconst]
    exact hlogU
  have hB := chapter09_unconditional_archimedean_B_tendsto
  have hC := chapter09_unconditional_archimedean_C_tendsto
  have hlimit : Tendsto
      (fun T : ℝ => chapter09UnconditionalInfiniteDegreeExponent T α₀)
      atTop
      (𝓝 (chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2)) := by
    have hbase : Tendsto
        (fun T : ℝ =>
          (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
            α₀ * (Real.pi / 2)) - chapter09BT T)
        atTop
        (𝓝 ((chapter09EulerMascheroni + Real.log (8 * Real.pi) +
            α₀ * (Real.pi / 2)) - Real.log 2)) := by
      simpa using (tendsto_const_nhds.sub hB)
    have hscaled : Tendsto (fun T : ℝ => α₀ * chapter09CT T)
        atTop (𝓝 (α₀ * (Real.pi / 2 - 1))) := by
      simpa [mul_comm] using hC.const_mul α₀
    have h := hbase.sub hscaled
    convert h using 1
    · simp only [chapter09UnconditionalInfiniteDegreeExponent]
    · ring_nf
  let gap : ℝ :=
    chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2 - Real.log U
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [hlogU']
  have hneighborhood : Set.Ioi (Real.log U + gap / 2) ∈
      𝓝 (chapter09EulerMascheroni + Real.log (8 * Real.pi) + α₀ - Real.log 2) := by
    apply Ioi_mem_nhds
    dsimp [gap]
    linarith
  have hevent := hlimit.eventually hneighborhood
  rcases (eventually_atTop.1 hevent) with ⟨R, hR⟩
  obtain ⟨n, hn⟩ := exists_nat_ge R
  let Tq : ℚ := n + 1
  have hTqR : R ≤ (Tq : ℝ) := by
    dsimp [Tq]
    have hn' : R ≤ (n : ℝ) := by exact_mod_cast hn
    norm_num at hn' ⊢
    linarith
  have hTqpos : 0 < (Tq : ℝ) := by
    dsimp [Tq]
    exact_mod_cast (Nat.succ_pos n)
  have hgapT : Real.log U <
      chapter09UnconditionalInfiniteDegreeExponent (Tq : ℝ) α₀ := by
    have hlarge := hR (Tq : ℝ) hTqR
    dsimp [gap] at hlarge
    linarith
  let gapT : ℝ :=
    chapter09UnconditionalInfiniteDegreeExponent (Tq : ℝ) α₀ - Real.log U
  have hgapTpos : 0 < gapT := by
    dsimp [gapT]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (Tq : ℝ) / gapT)
  have hNpos : 0 < N := by
    have hnum : 0 < 2 * (Tq : ℝ) / gapT := by positivity
    exact_mod_cast (show (0 : ℝ) < (N : ℝ) by linarith)
  have hNrealpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hmul : 2 * (Tq : ℝ) < gapT * (N : ℝ) := by
    have h := (div_lt_iff₀ hgapTpos).mp hN
    simpa [mul_comm] using h
  have hpole : 2 * (Tq : ℝ) / (N : ℝ) < gapT := by
    apply (div_lt_iff₀ hNrealpos).2
    simpa [mul_comm] using hmul
  exact ⟨⟨Tq, hTqpos, hgapT, N, hNpos, hpole⟩⟩

noncomputable def chapter09Threshold (U α₀ : ℝ) : ℕ :=
  if hUpos : 0 < U then
    if hU : U < chapter09UnconditionalAsymptoticConstant α₀ then
      (Classical.choice
        (chapter09_threshold_certificate_exists hUpos hU)).N
    else 0
  else 0

theorem chapter09_threshold_principle
    {U α₀ : ℝ}
    (hUpos : 0 < U)
    (hU : U < chapter09UnconditionalAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K],
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09Threshold U α₀ := by
  let C : chapter09ThresholdCertificate U α₀ :=
    Classical.choice (chapter09_threshold_certificate_exists hUpos hU)
  have hthreshold : chapter09Threshold U α₀ = C.N := by
    simp [chapter09Threshold, C, hUpos, hU]
  intro K _ _ hceil hα
  rw [hthreshold]
  by_contra hnot
  have hNle : C.N ≤ chapter09Degree K := Nat.le_of_not_gt hnot
  have hlogceil : Real.log (chapter09RootDiscriminant K) ≤ Real.log U := by
    exact Real.strictMonoOn_log.monotoneOn
      (show chapter09RootDiscriminant K ∈ Set.Ioi 0 from
        chapter09_root_discriminant_pos K)
      (show U ∈ Set.Ioi 0 from hUpos) hceil
  have hloglower := chapter09_universal_odlyzko_poitou_log_bound K C.T_pos
  let F : Chapter09TestFunction :=
    chapter09UnconditionalTestFunction (C.T : ℝ)
  have hAeq : chapter09A F = (C.T : ℝ) / 2 := by
    change chapter09UnconditionalPoleIntegral (C.T : ℝ) = (C.T : ℝ) / 2
    exact chapter09_unconditional_pole_integral C.T_pos
  have hA : 0 ≤ chapter09A F := by
    rw [hAeq]
    exact div_nonneg (le_of_lt C.T_pos) (by norm_num)
  have hC : chapter09C F < Real.pi / 2 := by
    simpa [F, chapter09CT] using
      (chapter09_unconditional_archimedean_C_lt_pi_div_two C.T_pos)
  have hmono := chapter09_fixed_certificate_covers_larger_degree_and_signature
    F hA hC C.N_pos hNle hα
  have hfixed :
      chapter09FixedTestFunctionLogBound F C.N α₀ =
        chapter09UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) := by
    unfold chapter09FixedTestFunctionLogBound chapter09FixedTestFunctionConstant
    rw [hAeq]
    simp [chapter09UnconditionalInfiniteDegreeExponent, chapter09BT,
      chapter09CT, F]
    ring
  have hexponent :
      chapter09UnconditionalExponent K (C.T : ℝ) =
        chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := by
    simpa [F] using
      (chapter09_unconditional_exponent_eq_fixed_test_function_log_bound
        K C.T_pos)
  have hfixedlower :
      chapter09UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) ≤
        chapter09UnconditionalExponent K (C.T : ℝ) := by
    calc
      chapter09UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
          2 * (C.T : ℝ) / (C.N : ℝ) =
          chapter09FixedTestFunctionLogBound F C.N α₀ := hfixed.symm
      _ ≤ chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := hmono
      _ = chapter09UnconditionalExponent K (C.T : ℝ) := hexponent.symm
  have hstrict : Real.log U <
      chapter09UnconditionalInfiniteDegreeExponent (C.T : ℝ) α₀ -
        2 * (C.T : ℝ) / (C.N : ℝ) := by
    linarith [C.pole_gap]
  linarith [hloglower, hlogceil, hfixedlower, hstrict]

structure chapter09GRHThresholdCertificate (U α₀ : ℝ) where
  T : ℚ
  T_pos : 0 < (T : ℝ)
  infinite_degree_gap :
    Real.log U < chapter09GRHInfiniteDegreeExponent (T : ℝ) α₀
  N : ℕ
  N_pos : 0 < N
  pole_gap :
    4 * chapter09GRHPoleIntegral (T : ℝ) / (N : ℝ) <
      chapter09GRHInfiniteDegreeExponent (T : ℝ) α₀ - Real.log U

theorem chapter09_grh_threshold_certificate_exists
    {U α₀ : ℝ} (hUpos : 0 < U)
    (hU : U < chapter09GRHAsymptoticConstant α₀) :
    Nonempty (chapter09GRHThresholdCertificate U α₀) := by
  have hconstpos : 0 < chapter09GRHAsymptoticConstant α₀ := by
    unfold chapter09GRHAsymptoticConstant
    positivity
  have hlogU : Real.log U < Real.log (chapter09GRHAsymptoticConstant α₀) := by
    exact Real.strictMonoOn_log
      (show U ∈ Set.Ioi 0 from hUpos)
      (show chapter09GRHAsymptoticConstant α₀ ∈ Set.Ioi 0 from hconstpos) hU
  have hlogconst :
      Real.log (chapter09GRHAsymptoticConstant α₀) =
        chapter09EulerMascheroni + Real.log (8 * Real.pi) +
          α₀ * (Real.pi / 2) := by
    rw [chapter09GRHAsymptoticConstant,
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  have hlogU' : Real.log U <
      chapter09EulerMascheroni + Real.log (8 * Real.pi) +
        α₀ * (Real.pi / 2) := by
    rw [← hlogconst]
    exact hlogU
  have hB := chapter09_grh_archimedean_B_tendsto
  have hC := chapter09_grh_archimedean_C_tendsto
  have hlimit : Tendsto
      (fun T : ℝ => chapter09GRHInfiniteDegreeExponent T α₀)
      atTop (𝓝 (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
        α₀ * (Real.pi / 2))) := by
    have hbase : Tendsto
        (fun T : ℝ => chapter09EulerMascheroni + Real.log (8 * Real.pi) +
          α₀ * (Real.pi / 2) - chapter09GRHBT T)
        atTop (𝓝 (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
          α₀ * (Real.pi / 2))) := by
      simpa using (tendsto_const_nhds.sub hB)
    have hscaled : Tendsto (fun T : ℝ => α₀ * chapter09GRHCT T)
        atTop (𝓝 0) := by
      simpa using hC.const_mul α₀
    have h := hbase.sub hscaled
    convert h using 1
    · simp only [chapter09GRHInfiniteDegreeExponent]
    · simp
  let gap : ℝ :=
    chapter09EulerMascheroni + Real.log (8 * Real.pi) +
      α₀ * (Real.pi / 2) - Real.log U
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [hlogU']
  have hneighborhood : Set.Ioi (Real.log U + gap / 2) ∈
      𝓝 (chapter09EulerMascheroni + Real.log (8 * Real.pi) +
        α₀ * (Real.pi / 2)) := by
    apply Ioi_mem_nhds
    dsimp [gap]
    linarith
  have hevent := hlimit.eventually hneighborhood
  rcases (eventually_atTop.1 hevent) with ⟨R, hR⟩
  obtain ⟨n, hn⟩ := exists_nat_ge R
  let Tq : ℚ := n + 1
  have hTqR : R ≤ (Tq : ℝ) := by
    dsimp [Tq]
    have hn' : R ≤ (n : ℝ) := by exact_mod_cast hn
    norm_num at hn' ⊢
    linarith
  have hTqpos : 0 < (Tq : ℝ) := by
    dsimp [Tq]
    exact_mod_cast (Nat.succ_pos n)
  have hgapT : Real.log U <
      chapter09GRHInfiniteDegreeExponent (Tq : ℝ) α₀ := by
    have hlarge := hR (Tq : ℝ) hTqR
    dsimp [gap] at hlarge
    linarith
  let gapT : ℝ :=
    chapter09GRHInfiniteDegreeExponent (Tq : ℝ) α₀ - Real.log U
  have hgapTpos : 0 < gapT := by
    dsimp [gapT]
    linarith
  have hP : 0 ≤ chapter09GRHPoleIntegral (Tq : ℝ) := by
    rw [chapter09_grh_pole_integral hTqpos]
    have hcosh : 1 ≤ Real.cosh ((Tq : ℝ) / 2) := Real.one_le_cosh _
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hcosh)
  obtain ⟨N, hN⟩ := exists_nat_gt
    (4 * chapter09GRHPoleIntegral (Tq : ℝ) / gapT)
  have hNpos : 0 < N := by
    have hnum : 0 ≤ 4 * chapter09GRHPoleIntegral (Tq : ℝ) / gapT :=
      div_nonneg (mul_nonneg (by positivity) hP) hgapTpos.le
    exact_mod_cast (show (0 : ℝ) < (N : ℝ) by linarith)
  have hNrealpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hmul : 4 * chapter09GRHPoleIntegral (Tq : ℝ) <
      gapT * (N : ℝ) := by
    have h := (div_lt_iff₀ hgapTpos).mp hN
    simpa [mul_comm] using h
  have hpole : 4 * chapter09GRHPoleIntegral (Tq : ℝ) / (N : ℝ) < gapT := by
    apply (div_lt_iff₀ hNrealpos).2
    simpa [mul_comm] using hmul
  exact ⟨⟨Tq, hTqpos, hgapT, N, hNpos, hpole⟩⟩

noncomputable def chapter09GRHThreshold (U α₀ : ℝ) : ℕ :=
  if hUpos : 0 < U then
    if hU : U < chapter09GRHAsymptoticConstant α₀ then
      (Classical.choice
        (chapter09_grh_threshold_certificate_exists hUpos hU)).N
    else 0
  else 0

theorem chapter09_grh_threshold_principle
    {U α₀ : ℝ}
    (hUpos : 0 < U)
    (hU : U < chapter09GRHAsymptoticConstant α₀) :
    ∀ (K : Type*) [Field K] [NumberField K]
      [Chapter09ZetaZeroInterface K],
      chapter09GRH K →
      chapter09RootDiscriminant K ≤ U →
      α₀ ≤ chapter09RealProportion K →
      chapter09Degree K < chapter09GRHThreshold U α₀ := by
  let C : chapter09GRHThresholdCertificate U α₀ :=
    Classical.choice (chapter09_grh_threshold_certificate_exists hUpos hU)
  have hthreshold : chapter09GRHThreshold U α₀ = C.N := by
    simp [chapter09GRHThreshold, C, hUpos, hU]
  intro K _ _ _ hgrh hceil hα
  rw [hthreshold]
  by_contra hnot
  have hNle : C.N ≤ chapter09Degree K := Nat.le_of_not_gt hnot
  have hlogceil : Real.log (chapter09RootDiscriminant K) ≤ Real.log U := by
    exact Real.strictMonoOn_log.monotoneOn
      (show chapter09RootDiscriminant K ∈ Set.Ioi 0 from
        chapter09_root_discriminant_pos K)
      (show U ∈ Set.Ioi 0 from hUpos) hceil
  have hexpbound := chapter09_grh_universal_odlyzko_poitou_bound
    K C.T_pos hgrh
  have hloglower : chapter09GRHExponent K (C.T : ℝ) ≤
      Real.log (chapter09RootDiscriminant K) := by
    rw [← Real.exp_le_exp]
    simpa [Real.exp_log (chapter09_root_discriminant_pos K)] using hexpbound
  let F : Chapter09TestFunction := chapter09GRHTestFunction (C.T : ℝ)
  have hAeq : chapter09A F = chapter09GRHPoleIntegral (C.T : ℝ) := by
    rfl
  have hA : 0 ≤ chapter09A F := by
    rw [hAeq, chapter09_grh_pole_integral C.T_pos]
    exact mul_nonneg
      (div_nonneg (by norm_num) (le_of_lt C.T_pos))
      (sub_nonneg.mpr (Real.one_le_cosh _))
  have hC : chapter09C F < Real.pi / 2 := by
    simpa [F, chapter09GRHCT] using
      (chapter09_grh_archimedean_C_lt_pi_div_two C.T_pos)
  have hmono := chapter09_fixed_certificate_covers_larger_degree_and_signature
    F hA hC C.N_pos hNle hα
  have hfixed :
      chapter09FixedTestFunctionLogBound F C.N α₀ =
        chapter09GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          4 * chapter09GRHPoleIntegral (C.T : ℝ) / (C.N : ℝ) := by
    unfold chapter09FixedTestFunctionLogBound chapter09FixedTestFunctionConstant
    rw [hAeq]
    simp [chapter09GRHInfiniteDegreeExponent, chapter09GRHBT,
      chapter09GRHCT, F]
    ring
  have hexponent :
      chapter09GRHExponent K (C.T : ℝ) =
        chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := by
    unfold chapter09GRHExponent chapter09FixedTestFunctionLogBound
      chapter09FixedTestFunctionConstant
    rw [hAeq]
    simp [chapter09GRHBT, chapter09GRHCT, F]
    ring
  have hfixedlower :
      chapter09GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          4 * chapter09GRHPoleIntegral (C.T : ℝ) / (C.N : ℝ) ≤
        chapter09GRHExponent K (C.T : ℝ) := by
    calc
      chapter09GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
          4 * chapter09GRHPoleIntegral (C.T : ℝ) / (C.N : ℝ) =
          chapter09FixedTestFunctionLogBound F C.N α₀ := hfixed.symm
      _ ≤ chapter09FixedTestFunctionLogBound F
          (chapter09Degree K) (chapter09RealProportion K) := hmono
      _ = chapter09GRHExponent K (C.T : ℝ) := hexponent.symm
  have hstrict : Real.log U <
      chapter09GRHInfiniteDegreeExponent (C.T : ℝ) α₀ -
        4 * chapter09GRHPoleIntegral (C.T : ℝ) / (C.N : ℝ) := by
    linarith [C.pole_gap]
  linarith [hloglower, hlogceil, hfixedlower, hstrict]

def chapter09StrictUnconditionalThresholdCondition
    (U α₀ : ℝ) : Prop :=
  0 < U ∧ U < chapter09UnconditionalAsymptoticConstant α₀

def chapter09StrictGRHThresholdCondition (U α₀ : ℝ) : Prop :=
  0 < U ∧ U < chapter09GRHAsymptoticConstant α₀

theorem chapter09_unconditional_equality_is_not_strict_threshold
    (α₀ : ℝ) :
    ¬ chapter09StrictUnconditionalThresholdCondition
      (chapter09UnconditionalAsymptoticConstant α₀) α₀ := by
  intro h
  exact (lt_irrefl _ h.2)

theorem chapter09_grh_equality_is_not_strict_threshold
    (α₀ : ℝ) :
    ¬ chapter09StrictGRHThresholdCondition
      (chapter09GRHAsymptoticConstant α₀) α₀ := by
  intro h
  exact (lt_irrefl _ h.2)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
