import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section02TheTriangularAutocorrelation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.ZetaValues

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

/-! ## 8.3 Exact evaluation of the archimedean terms -/

def chapter08BT (T : ℝ) : ℝ :=
  chapter08B (chapter08FUnconditionalTriangle T)

def chapter08CT (T : ℝ) : ℝ :=
  chapter08C (chapter08FUnconditionalTriangle T)

def chapter08Coth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

def chapter08Odd (k : ℕ) : ℝ :=
  ((2 * k + 1 : ℕ) : ℝ)

def chapter08BSeriesTerm (T : ℝ) (k : ℕ) : ℝ :=
  ((1 + chapter08Odd k * T) * Real.exp (-chapter08Odd k * T)) /
    (chapter08Odd k) ^ 2

def chapter08BSeriesTail (T : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, chapter08BSeriesTerm T (m + 1 + k)

theorem chapter08_B_series_coefficient_bound
    {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    (1 + chapter08Odd k * T) / (chapter08Odd k) ^ 2 ≤ 1 + T := by
  have hodd : (1 : ℝ) ≤ chapter08Odd k := by
    dsimp [chapter08Odd]
    have hodd_nat : 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast hodd_nat
  have hodd_pos : 0 < chapter08Odd k := lt_of_lt_of_le zero_lt_one hodd
  apply (div_le_iff₀ (sq_pos_of_pos hodd_pos)).2
  have h₁ : 0 ≤ (chapter08Odd k) ^ 2 - 1 := by nlinarith
  have h₂ : 0 ≤ T * ((chapter08Odd k) ^ 2 - chapter08Odd k) := by
    apply mul_nonneg hT
    nlinarith
  nlinarith

theorem chapter08_B_series_summable {T : ℝ} (hT : 0 < T) :
    Summable (chapter08BSeriesTerm T) := by
  have hq : ‖Real.exp (-2 * T)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun k : ℕ => (Real.exp (-2 * T)) ^ k) :=
    summable_geometric_of_norm_lt_one hq
  have hmajor : Summable (fun k : ℕ =>
      ((1 + T) * Real.exp (-T)) * (Real.exp (-2 * T)) ^ k) :=
    hgeom.mul_left ((1 + T) * Real.exp (-T))
  apply Summable.of_norm_bounded_eventually_nat hmajor
  filter_upwards [] with k
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hcoef := chapter08_B_series_coefficient_bound (le_of_lt hT) k
    have hexp : Real.exp (-chapter08Odd k * T) =
        Real.exp (-T) * (Real.exp (-2 * T)) ^ k := by
      dsimp [chapter08Odd]
      rw [show -((2 * k + 1 : ℕ) : ℝ) * T = -T + (-2 * T) * k by
        push_cast
        ring]
      rw [Real.exp_add]
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    have hterm_nonneg : 0 ≤ chapter08BSeriesTerm T k := by
      rw [chapter08BSeriesTerm]
      have hodd_pos : 0 < chapter08Odd k := by
        dsimp [chapter08Odd]
        positivity
      exact div_nonneg (mul_nonneg (by nlinarith) (Real.exp_nonneg _)) (sq_nonneg _)
    rw [chapter08BSeriesTerm, hexp]
    have hform :
        ((1 + chapter08Odd k * T) * (Real.exp (-T) * (Real.exp (-2 * T)) ^ k)) /
            (chapter08Odd k) ^ 2 =
          ((1 + chapter08Odd k * T) / (chapter08Odd k) ^ 2) *
            (Real.exp (-T) * (Real.exp (-2 * T)) ^ k) := by
      ring
    rw [hform]
    calc
      ((1 + chapter08Odd k * T) / (chapter08Odd k) ^ 2) *
          (Real.exp (-T) * (Real.exp (-2 * T)) ^ k) ≤
        (1 + T) * (Real.exp (-T) * (Real.exp (-2 * T)) ^ k) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (1 + T) * Real.exp (-T) * (Real.exp (-2 * T)) ^ k := by ring
  · rw [chapter08BSeriesTerm]
    have hodd_pos : 0 < chapter08Odd k := by
      dsimp [chapter08Odd]
      positivity
    exact div_nonneg (mul_nonneg (by nlinarith) (Real.exp_nonneg _)) (sq_nonneg _)

theorem chapter08_B_limiting_integral_data :
    IntegrableOn
        (fun x : ℝ => (1 - 1 / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) =
        Real.log 2 := by
  have hscale : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (f := fun x : ℝ => x) (l := Filter.atTop)
      (by norm_num : (0 : ℝ) < 1 / 2)).2 Filter.tendsto_id
  have hexp_neg : Filter.Tendsto (fun x : ℝ => Real.exp (-x))
      Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hbase_deriv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
      (1 / (2 * Real.cosh (x / 2))) x := by
    intro x hx
    have he := (Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)
    have ha := (Real.hasDerivAt_arctan (Real.exp (x / 2))).comp x he
    have ha' : HasDerivAt (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
        (2 * (1 / (1 + Real.exp (x / 2) ^ 2) *
          (Real.exp (x / 2) * (1 / 2)))) x := by
      simpa only [Function.comp_apply, id_eq] using ha.const_mul 2
    convert ha' using 1
    rw [Real.cosh_eq]
    field_simp [Real.exp_ne_zero]
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    have hxexp : x / 2 + -(x / 2) = 0 := by ring
    rw [hxexp, Real.exp_zero]
    rw [pow_two, ← Real.exp_add]
    ring_nf
  have hbase_pos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ 1 / (2 * Real.cosh (x / 2)) := by
    intro x hx
    positivity
  have hbase_tendsto : Filter.Tendsto
      (fun x : ℝ => 2 * Real.arctan (Real.exp (x / 2)))
      Filter.atTop (nhds Real.pi) := by
    have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (x / 2))
        Filter.atTop Filter.atTop := by
      have h := Real.tendsto_exp_atTop.comp hscale
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
    have harc : Filter.Tendsto
        (fun x : ℝ => Real.arctan (Real.exp (x / 2)))
        Filter.atTop (nhds (Real.pi / 2)) := by
      have h := Real.tendsto_arctan_atTop.comp hexp
      exact tendsto_nhds_of_tendsto_nhdsWithin
        (by simpa [Function.comp_def] using h)
    have hmul := harc.const_mul (2 : ℝ)
    have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [hpi] at hmul
    exact hmul
  have htanh_deriv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.tanh (y / 2))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
    intro x
    have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_sinh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_cosh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hq := hs.div hc (ne_of_gt (Real.cosh_pos (x / 2)))
    have hfun : (fun y : ℝ => Real.tanh (y / 2)) =
        (fun y : ℝ => Real.sinh (y / 2) / Real.cosh (y / 2)) := by
      funext y
      rw [Real.tanh_eq_sinh_div_cosh]
    rw [hfun]
    apply hq.congr_deriv
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have htanh_formula : ∀ z : ℝ,
      Real.tanh z = (1 - Real.exp (-2 * z)) / (1 + Real.exp (-2 * z)) := by
    intro z
    rw [Real.tanh_eq]
    have hprod : Real.exp z * Real.exp (-z) = 1 := by
      rw [← Real.exp_add]
      simp
    have hsq : Real.exp (-2 * z) = Real.exp (-z) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
    have ha : Real.exp z = 1 / Real.exp (-z) := by
      apply (eq_div_iff (Real.exp_ne_zero _)).2
      simpa using hprod
    have hden₁ : Real.exp z + Real.exp (-z) ≠ 0 := by positivity
    have hden₂ : 1 + Real.exp (-z) ^ 2 ≠ 0 := by positivity
    rw [ha]
    field_simp [hden₁, hden₂, Real.exp_ne_zero]
  have htanh_tendsto : Filter.Tendsto
      (fun x : ℝ => Real.tanh (x / 2)) Filter.atTop (nhds 1) := by
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
      have hnum : ContinuousAt (fun y : ℝ => 1 - y) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have hden : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact hnum.div₀ hden (by norm_num)
    have h := hcont.tendsto.comp hexp_neg
    have h' : Filter.Tendsto
        (fun x : ℝ => (1 - Real.exp (-x)) / (1 + Real.exp (-x)))
        Filter.atTop (nhds 1) := by
      convert h using 1 <;> simp [Function.comp_def]
    have heq : ∀ x : ℝ, Real.tanh (x / 2) =
        (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
      intro x
      rw [htanh_formula]
      have harg : -2 * (x / 2) = -x := by ring
      rw [harg]
    simpa [heq] using h'
  have hQderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => Real.log (1 + Real.exp (-y)) -
        2 * Real.log (1 + Real.exp (-(y / 2))))
      ((1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) x := by
    intro x hx
    have harg₁ : HasDerivAt (fun y : ℝ => 1 + Real.exp (-y))
        (-Real.exp (-x)) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add
          ((Real.hasDerivAt_exp (-x)).comp x
            ((hasDerivAt_id x).neg)) using 1
      all_goals first | rfl | ring
    have hlog₁ : HasDerivAt (fun y : ℝ => Real.log (1 + Real.exp (-y)))
        (-Real.exp (-x) / (1 + Real.exp (-x))) x := by
      have hl := (Real.hasDerivAt_log (by positivity :
        1 + Real.exp (-x) ≠ 0)).comp x harg₁
      have hfun : (fun y : ℝ => Real.log (1 + Real.exp (-y))) =
          (Real.log ∘ fun y : ℝ => 1 + Real.exp (-y)) := by
        funext y
        rfl
      rw [hfun]
      apply hl.congr_deriv
      field_simp
    have harg₂ : HasDerivAt (fun y : ℝ => 1 + Real.exp (-(y / 2)))
        (-Real.exp (-(x / 2)) / 2) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add
          ((Real.hasDerivAt_exp (-(x / 2))).comp x
            ((hasDerivAt_id x).div_const 2 |>.neg)) using 1
      all_goals first | rfl | ring
    have hlog₂ : HasDerivAt
        (fun y : ℝ => Real.log (1 + Real.exp (-(y / 2))))
        ((-Real.exp (-(x / 2)) / 2) / (1 + Real.exp (-(x / 2)))) x := by
      have hl := (Real.hasDerivAt_log (by positivity :
        1 + Real.exp (-(x / 2)) ≠ 0)).comp x harg₂
      have hfun : (fun y : ℝ => Real.log (1 + Real.exp (-(y / 2)))) =
          (Real.log ∘ fun y : ℝ => 1 + Real.exp (-(y / 2))) := by
        funext y
        rfl
      rw [hfun]
      apply hl.congr_deriv
      field_simp
    have hsub := hlog₁.sub (hlog₂.const_mul 2)
    convert hsub using 1 <;>
      first
      | rfl
      | simp only [Pi.sub_apply, Pi.const_mul_apply, Function.comp_apply, id_eq]
      | by_cases hx0 : x = 0
        · subst x
          norm_num [Real.cosh_zero, Real.sinh_zero, Real.exp_zero]
        · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
          have hdiff : Real.exp (x / 2) - Real.exp (-(x / 2)) ≠ 0 := by
            apply ne_of_gt
            apply sub_pos.mpr
            exact Real.exp_lt_exp.mpr (by linarith)
          rw [Real.cosh_eq, Real.sinh_eq]
          field_simp [Real.exp_ne_zero, hdiff]
          have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
            rw [← Real.exp_add]
            simp
          have hsq : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
          have ha : Real.exp (x / 2) = 1 / Real.exp (-(x / 2)) := by
            apply (eq_div_iff (Real.exp_ne_zero _)).2
            simpa using hprod
          rw [hsq, ha]
          field_simp [Real.exp_ne_zero, hdiff]
          ring
  have hQpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)) := by
    intro x hx
    have hxpos : 0 < x := hx
    have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
    have hinv : 1 / Real.cosh (x / 2) ≤ 1 := by
      rw [div_le_iff₀ (Real.cosh_pos _)]
      nlinarith
    have hsinh : 0 < Real.sinh (x / 2) := by
      rw [Real.sinh_pos_iff]
      linarith
    exact div_nonneg (sub_nonneg.mpr hinv) (by positivity)
  have hQ_tendsto : Filter.Tendsto
      (fun x : ℝ => Real.log (1 + Real.exp (-x)) -
        2 * Real.log (1 + Real.exp (-(x / 2))))
      Filter.atTop (nhds 0) := by
    have hlogcont : ContinuousAt (fun y : ℝ => Real.log (1 + y)) 0 := by
      have harg : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact harg.log (by norm_num)
    have h₁ := hlogcont.tendsto.comp hexp_neg
    have hneg_half : Filter.Tendsto (fun x : ℝ => Real.exp (-(x / 2)))
        Filter.atTop (nhds 0) := by
      have h := hexp_neg.comp hscale
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
    have h₂ := hlogcont.tendsto.comp hneg_half
    have h₁' : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.exp (-x)))
        Filter.atTop (nhds 0) := by
      convert h₁ using 1 <;> simp [Function.comp_def]
    have h₂' : Filter.Tendsto
        (fun x : ℝ => Real.log (1 + Real.exp (-(x / 2))))
        Filter.atTop (nhds 0) := by
      convert h₂ using 1 <;> simp [Function.comp_def]
    simpa using h₁'.sub (h₂'.const_mul 2)
  have hQint := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun x : ℝ => Real.log (1 + Real.exp (-x)) -
      2 * Real.log (1 + Real.exp (-(x / 2))))
    (g' := fun x : ℝ =>
      (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)))
    (a := (0 : ℝ)) (l := (0 : ℝ)) hQderiv hQpos hQ_tendsto
  have hQzero :
      (Real.log (1 + Real.exp (-(0 : ℝ))) -
        2 * Real.log (1 + Real.exp (-((0 : ℝ) / 2)))) = -Real.log 2 := by
    norm_num [Real.exp_zero]
    ring
  have hBlim :
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) =
        Real.log 2 := by
    rw [hQint, hQzero]
    ring
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' hQderiv hQpos hQ_tendsto,
    hBlim⟩

theorem chapter08_B_correction_tail {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x : ℝ => 1 / Real.sinh x) (Ioi T) ∧
      (∫ x : ℝ in Ioi T, 1 / Real.sinh x) =
        Real.log (chapter08Coth (T / 2)) := by
  have hderiv : ∀ x ∈ Ici T, HasDerivAt
      (fun y : ℝ => Real.log (Real.tanh (y / 2)))
      (1 / Real.sinh x) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hT hx
    have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_sinh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_cosh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have ht := hs.div hc (ne_of_gt (Real.cosh_pos (x / 2)))
    have htan : HasDerivAt (fun y : ℝ => Real.tanh (y / 2))
        (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
      have hfun : (fun y : ℝ => Real.tanh (y / 2)) =
          (fun y : ℝ => Real.sinh (y / 2) / Real.cosh (y / 2)) := by
        funext y
        rw [Real.tanh_eq_sinh_div_cosh]
      rw [hfun]
      apply ht.congr_deriv
      field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
      nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
    have htanpos : 0 < Real.tanh (x / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (by rw [Real.sinh_pos_iff]; linarith) (Real.cosh_pos _)
    have hlog := (Real.hasDerivAt_log (ne_of_gt htanpos)).comp x htan
    have hfun : (fun y : ℝ => Real.log (Real.tanh (y / 2))) =
        (Real.log ∘ fun y : ℝ => Real.tanh (y / 2)) := by
      funext y
      rfl
    rw [hfun]
    apply hlog.congr_deriv
    have hsinh : 0 < Real.sinh (x / 2) := by
      rw [Real.sinh_pos_iff]
      linarith
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos (x / 2)), ne_of_gt hsinh]
    simp only [Real.sinh_eq, Real.cosh_eq]
    field_simp [Real.exp_ne_zero]
    have hxp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hxn : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hxp, hxn]
    ring
  have hpos : ∀ x ∈ Ioi T, 0 ≤ 1 / Real.sinh x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hT hx
    have hsinh : 0 < Real.sinh x := by
      rw [Real.sinh_pos_iff]
      linarith
    positivity
  have hexp_neg : Filter.Tendsto (fun x : ℝ => Real.exp (-x))
      Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have htan : Filter.Tendsto (fun x : ℝ => Real.tanh (x / 2))
      Filter.atTop (nhds 1) := by
    have hscale : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos
        (f := fun x : ℝ => x) (l := Filter.atTop)
        (by norm_num : (0 : ℝ) < 1 / 2)).2 Filter.tendsto_id
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
      have hnum : ContinuousAt (fun y : ℝ => 1 - y) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have hden : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact hnum.div₀ hden (by norm_num)
    have h := hcont.tendsto.comp hexp_neg
    have h' : Filter.Tendsto
        (fun x : ℝ => (1 - Real.exp (-x)) / (1 + Real.exp (-x)))
        Filter.atTop (nhds 1) := by
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
  have hlog_tendsto : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.tanh (x / 2)))
      Filter.atTop (nhds 0) := by
    have h := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have h' := h.tendsto.comp htan
    simpa only [Function.comp_def, Real.log_one] using h'
  have hcalc := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun x : ℝ => Real.log (Real.tanh (x / 2)))
    (g' := fun x : ℝ => 1 / Real.sinh x)
    (a := T) (l := (0 : ℝ)) hderiv hpos hlog_tendsto
  have htan_pos : 0 < Real.tanh (T / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (by rw [Real.sinh_pos_iff]; linarith) (Real.cosh_pos _)
  have hcot : chapter08Coth (T / 2) = (Real.tanh (T / 2))⁻¹ := by
    unfold chapter08Coth
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos (T / 2)), ne_of_gt
      (by rw [Real.sinh_pos_iff]; linarith : 0 < Real.sinh (T / 2))]
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlog_tendsto, ?_⟩
  rw [hcalc, hcot, Real.log_inv]
  simp

theorem chapter08_B_exact_formula {T : ℝ} (hT : 0 < T) :
    chapter08BT T =
      Real.log 2 + Real.pi ^ 2 / (4 * T) +
        Real.log (chapter08Coth (T / 2)) -
        (2 / T) * (∑' k : ℕ, chapter08BSeriesTerm T k) := by
  let f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have htotal : HasSum f (Real.pi ^ 2 / 6) := by
    simpa [f] using hasSum_zeta_two
  have htail : Summable (fun k : ℕ => f (k + 1)) :=
    (summable_nat_add_iff 1).2 htotal.summable
  have hodd_summable : Summable (fun k : ℕ => f (2 * k + 1)) := by
    apply htail.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [f]
      have hk₁ : 0 < (k : ℝ) + 1 := by positivity
      have hk₂ : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
        push_cast
        nlinarith
      simpa using (one_div_le_one_div_of_le (sq_pos_of_pos hk₁) hsq)
    · dsimp [f]
      positivity
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1))
      (∑' k : ℕ, f (2 * k + 1)) := hodd_summable.hasSum
  have heven0 : HasSum (fun k : ℕ => (1 / 4 : ℝ) * f k)
      ((1 / 4 : ℝ) * (Real.pi ^ 2 / 6)) := htotal.mul_left _
  have heven : HasSum (fun k : ℕ => f (2 * k)) (Real.pi ^ 2 / 24) := by
    convert heven0 using 1
    · funext k
      dsimp [f]
      by_cases hk : k = 0
      · simp [hk]
      · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        push_cast
        field_simp [hk']
        ring
    · ring
  have hsplit : HasSum f (Real.pi ^ 2 / 24 + ∑' k : ℕ, f (2 * k + 1)) := by
    exact HasSum.even_add_odd heven hodd
  have hodd_sum : (∑' k : ℕ, f (2 * k + 1)) = Real.pi ^ 2 / 8 := by
    have h₁ := htotal.tsum_eq
    have h₂ := hsplit.tsum_eq
    linarith
  have hmoment : ∀ a c : ℝ, 0 < a → 0 ≤ c →
      IntegrableOn (fun x : ℝ => x * Real.exp (-a * x)) (Ioi c) ∧
        (∫ x : ℝ in Ioi c, x * Real.exp (-a * x)) =
          Real.exp (-a * c) * (a * c + 1) / a ^ 2 := by
    intro a c ha hc
    let g : ℝ → ℝ := fun x => -(x / a + 1 / a ^ 2) * Real.exp (-a * x)
    have hderiv : ∀ x ∈ Ici c,
        HasDerivAt g (x * Real.exp (-a * x)) x := by
      intro x hx
      have he : HasDerivAt (fun y : ℝ => Real.exp (-a * y))
          (-a * Real.exp (-a * x)) x := by
        simpa [Function.comp_def, mul_comm] using
          (Real.hasDerivAt_exp (-a * x)).comp x
            ((hasDerivAt_id x).const_mul (-a))
      have hl : HasDerivAt (fun y : ℝ => -(y / a + 1 / a ^ 2))
          (-1 / a) x := by
        have h₀ := (hasDerivAt_const x (-(1 / a ^ 2))).sub
            ((hasDerivAt_id x).div_const a)
        have hfun :
            (fun y : ℝ => -(y / a + 1 / a ^ 2)) =
              (fun x : ℝ => -(1 / a ^ 2)) - fun x : ℝ => id x / a := by
          funext y
          dsimp [id]
          ring
        have hder : (-1 / a : ℝ) = 0 - 1 / a := by ring
        rw [hfun, hder]
        exact h₀
      have hp := hl.mul he
      have hfun : g =
          (fun y : ℝ => -(y / a + 1 / a ^ 2)) *
            (fun y : ℝ => Real.exp (-a * y)) := by
        funext y
        rfl
      have hder : x * Real.exp (-a * x) =
          (-1 / a) * Real.exp (-a * x) +
            -(x / a + 1 / a ^ 2) * (-a * Real.exp (-a * x)) := by
        field_simp [ne_of_gt ha]
        ring
      rw [hfun, hder]
      exact hp
    have hpos : ∀ x ∈ Ioi c, 0 ≤ x * Real.exp (-a * x) := by
      intro x hx
      exact mul_nonneg (le_trans hc (le_of_lt hx)) (Real.exp_nonneg _)
    have hscale : Tendsto (fun x : ℝ => a * x) atTop atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos
          (f := fun x : ℝ => x) (l := Filter.atTop) ha).2
        Filter.tendsto_id
    have hpow := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
    have hxe : Tendsto (fun x : ℝ => x * Real.exp (-a * x)) atTop (nhds 0) := by
      have h := hpow.const_mul (1 / a)
      convert h using 1
      · funext x
        dsimp
        field_simp [ne_of_gt ha]
      · ring_nf
    have hexp : Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (nhds 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
      simpa [Function.comp_def] using h
    have hlim : Tendsto g atTop (nhds 0) := by
      have h₁ := hxe.const_mul (-(1 / a))
      have h₂ := hexp.const_mul (-(1 / a ^ 2))
      have h := h₁.add h₂
      convert h using 1
      · funext x
        dsimp [g]
        field_simp [ne_of_gt ha]
        ring
      · simp
    refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
    have hcalc := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
    calc
      (∫ x : ℝ in Ioi c, x * Real.exp (-a * x)) = 0 - g c := hcalc
      _ = Real.exp (-a * c) * (a * c + 1) / a ^ 2 := by
        dsimp [g]
        field_simp [ne_of_gt ha]
        ring
  have hsinh_double : ∀ x : ℝ,
      Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    intro x
    simp only [Real.sinh_eq, Real.cosh_eq]
    have hxp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hxn : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hxp, hxn]
    ring
  have hxsinh_int : IntegrableOn (fun x : ℝ => x / Real.sinh x) (Ioc 0 T) := by
    apply Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ))
      (s := Ioc 0 T) (M := 1) (ne_of_lt measure_Ioc_lt_top)
    · exact (measurable_id.div
        (Real.continuous_sinh.measurable.comp measurable_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hsinh : 0 < Real.sinh x := by
        rw [Real.sinh_pos_iff]
        exact hxpos
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hxpos.le hsinh.le)]
      apply (div_le_iff₀ hsinh).2
      simpa using (Real.self_le_sinh_iff.mpr hxpos.le)
  have hterm_int_iOi : ∀ k : ℕ,
      IntegrableOn
        (fun x : ℝ => 2 * (x * Real.exp (-chapter08Odd k * x))) (Ioi 0) := by
    intro k
    have hk : 0 < chapter08Odd k := by
      dsimp [chapter08Odd]
      positivity
    have h := (hmoment (chapter08Odd k) 0 hk (by positivity)).1
    show Integrable
      (fun x : ℝ => 2 * (x * Real.exp (-chapter08Odd k * x)))
      (volume.restrict (Ioi 0))
    simpa only [mul_comm] using h.integrable.const_mul 2
  have hterm_int_ioc : ∀ k : ℕ,
      IntegrableOn
        (fun x : ℝ => 2 * (x * Real.exp (-chapter08Odd k * x))) (Ioc 0 T) := by
    intro k
    exact (hterm_int_iOi k).mono_set Ioc_subset_Ioi_self
  have hterm_integral_ioc : ∀ k : ℕ,
      (∫ x : ℝ in Ioc 0 T,
        2 * (x * Real.exp (-chapter08Odd k * x))) =
        2 * (1 / (chapter08Odd k) ^ 2 -
          Real.exp (-chapter08Odd k * T) *
            (chapter08Odd k * T + 1) / (chapter08Odd k) ^ 2) := by
    intro k
    have hk : 0 < chapter08Odd k := by
      dsimp [chapter08Odd]
      positivity
    have h0 := (hmoment (chapter08Odd k) 0 hk (by positivity)).2
    have hT' := (hmoment (chapter08Odd k) T hk hT.le).2
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => x * Real.exp (-chapter08Odd k * x))
      (a := (0 : ℝ)) (b := T)
      (hmoment (chapter08Odd k) 0 hk (by positivity)).1
      (hmoment (chapter08Odd k) T hk hT.le).1
    rw [intervalIntegral.integral_of_le hT.le] at hadd
    have hinter :
      (∫ x : ℝ in Ioc 0 T,
          x * Real.exp (-chapter08Odd k * x)) =
          (∫ x : ℝ in Ioi 0, x * Real.exp (-chapter08Odd k * x)) -
      (∫ x : ℝ in Ioi T, x * Real.exp (-chapter08Odd k * x)) := by
      have hsub :
          (∫ x : ℝ in Ioc 0 T,
            x * Real.exp (-chapter08Odd k * x)) =
            (∫ x : ℝ in Ioi 0, x * Real.exp (-chapter08Odd k * x)) -
              (∫ x : ℝ in Ioi T, x * Real.exp (-chapter08Odd k * x)) := by
        linarith [hadd]
      exact hsub
    rw [integral_const_mul, hinter, h0, hT']
    norm_num
  have hnorm_bound_ioc : ∀ k : ℕ,
      (∫ x : ℝ in Ioc 0 T,
        ‖2 * (x * Real.exp (-chapter08Odd k * x))‖) ≤
        2 * f (2 * k + 1) := by
    intro k
    have hmeasure :
        (volume : Measure ℝ).restrict (Ioc 0 T) ≤
          (volume : Measure ℝ).restrict (Ioi 0) := by
      exact Measure.restrict_mono_set volume Ioc_subset_Ioi_self
    have hae : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)]
        (fun x : ℝ => ‖2 * (x * Real.exp (-chapter08Odd k * x))‖) :=
      Filter.Eventually.of_forall (fun x => norm_nonneg _)
    have hmono := MeasureTheory.integral_mono_measure hmeasure hae
      ((hterm_int_iOi k).integrable.norm)
    have hnorm :
        (∫ x : ℝ in Ioi 0,
          ‖2 * (x * Real.exp (-chapter08Odd k * x))‖) = 2 * f (2 * k + 1) := by
      have hnormfun :
          (∫ x : ℝ in Ioi 0,
            ‖2 * (x * Real.exp (-chapter08Odd k * x))‖) =
            ∫ x : ℝ in Ioi 0, 2 * (x * Real.exp (-chapter08Odd k * x)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg]
        have hxpos : 0 < x := hx
        exact mul_nonneg (by positivity)
          (mul_nonneg hxpos.le (Real.exp_nonneg _))
      rw [hnormfun, integral_const_mul]
      rw [(hmoment (chapter08Odd k) 0 (by
        dsimp [chapter08Odd]
        positivity) (by positivity)).2]
      norm_num [f, chapter08Odd]
    rw [hnorm] at hmono
    exact hmono
  have hnorm_summable_ioc : Summable (fun k : ℕ =>
      ∫ x : ℝ in Ioc 0 T,
        ‖2 * (x * Real.exp (-chapter08Odd k * x))‖) := by
    have hmajor := hodd_summable.mul_left (2 : ℝ)
    apply Summable.of_norm_bounded_eventually_nat hmajor
    filter_upwards [] with k
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hnorm_bound_ioc k
    · exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))
  have hgeom_ioc : ∀ x ∈ Ioc (0 : ℝ) T,
      (∑' k : ℕ, 2 * (x * Real.exp (-chapter08Odd k * x))) =
        x / Real.sinh x := by
    intro x hx
    have hxpos : 0 < x := hx.1
    let q : ℝ := Real.exp (-2 * x)
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact Real.exp_nonneg _
    have hq1 : q < 1 := by
      dsimp [q]
      rw [Real.exp_lt_one_iff]
      linarith
    have hgeo : HasSum (fun k : ℕ => q ^ k) (1 - q)⁻¹ :=
      hasSum_geometric_of_lt_one hq0 hq1
    have hs : HasSum (fun k : ℕ =>
        2 * (x * Real.exp (-chapter08Odd k * x)))
        ((2 * x * Real.exp (-x)) * (1 - q)⁻¹) := by
      apply (hgeo.mul_left (2 * x * Real.exp (-x))).congr
      intro s
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [q, chapter08Odd]
      rw [show -((2 * k + 1 : ℕ) : ℝ) * x =
          -x + (-2 * x) * k by
        push_cast
        ring]
      rw [Real.exp_add, ← Real.exp_nat_mul]
      ring_nf
    calc
      (∑' k : ℕ, 2 * (x * Real.exp (-chapter08Odd k * x))) =
          (2 * x * Real.exp (-x)) * (1 - q)⁻¹ := hs.tsum_eq
      _ = x / Real.sinh x := by
        have hqne : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
        have hsinh : 0 < Real.sinh x := by
          rw [Real.sinh_pos_iff]
          exact hxpos
        dsimp [q]
        rw [Real.sinh_eq]
        field_simp [hqne, Real.exp_ne_zero, ne_of_gt hsinh]
        have hprod : Real.exp x * Real.exp (-x) = 1 := by
          rw [← Real.exp_add]
          simp
        have hsq : Real.exp (-(2 * x)) = Real.exp (-x) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        have ha : Real.exp x = 1 / Real.exp (-x) := by
          apply (eq_div_iff (Real.exp_ne_zero _)).2
          simpa using hprod
        rw [hsq, ha]
        field_simp [Real.exp_ne_zero]
  have hinter_ioc := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := (volume : Measure ℝ).restrict (Ioc 0 T))
    hterm_int_ioc hnorm_summable_ioc
  have hfinite_series :
      (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) =
        Real.pi ^ 2 / 4 -
          2 * (∑' k : ℕ, chapter08BSeriesTerm T k) := by
    calc
      (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) =
          ∫ x : ℝ in Ioc 0 T,
            (∑' k : ℕ, 2 * (x * Real.exp (-chapter08Odd k * x))) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact (hgeom_ioc x hx).symm
      _ = ∑' k : ℕ, ∫ x : ℝ in Ioc 0 T,
          2 * (x * Real.exp (-chapter08Odd k * x)) := hinter_ioc.symm
      _ = ∑' k : ℕ, (2 * f (2 * k + 1) -
          2 * chapter08BSeriesTerm T k) := by
        apply tsum_congr
        intro k
        rw [hterm_integral_ioc]
        rw [chapter08BSeriesTerm]
        have hk : 0 < chapter08Odd k := by
          dsimp [chapter08Odd]
          positivity
        have hfodd : f (2 * k + 1) = 1 / (chapter08Odd k) ^ 2 := by
          dsimp [f, chapter08Odd]
        have hexp : Real.exp (-chapter08Odd k * T) =
            Real.exp (-T * chapter08Odd k) := by
          congr 1
          ring
        rw [hfodd, hexp]
        field_simp [ne_of_gt hk]
        ring
      _ = (∑' k : ℕ, 2 * f (2 * k + 1)) -
          ∑' k : ℕ, 2 * chapter08BSeriesTerm T k := by
        have h₁ := hodd_summable.mul_left (2 : ℝ)
        have h₂ := (chapter08_B_series_summable hT).mul_left (2 : ℝ)
        exact (h₁.hasSum.sub h₂.hasSum).tsum_eq
      _ = Real.pi ^ 2 / 4 -
          2 * (∑' k : ℕ, chapter08BSeriesTerm T k) := by
        rw [tsum_mul_left, tsum_mul_left, hodd_sum]
        ring_nf
  have hbase_data := chapter08_B_limiting_integral_data
  have htail_data := chapter08_B_correction_tail hT
  have hbase_ioc : IntegrableOn
      (fun x : ℝ => (1 - 1 / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2))) (Ioc 0 T) :=
    hbase_data.1.mono_set Ioc_subset_Ioi_self
  have hbase_tail : IntegrableOn
      (fun x : ℝ => (1 - 1 / Real.cosh (x / 2)) /
        (2 * Real.sinh (x / 2))) (Ioi T) :=
    hbase_data.1.mono_set (Ioi_subset_Ioi hT.le)
  have hcorr_ioc : IntegrableOn
      (fun x : ℝ => x / (T * Real.sinh x)) (Ioc 0 T) := by
    have h := hxsinh_int.integrable.const_mul (T⁻¹)
    apply h.congr
    filter_upwards [] with x
    field_simp [ne_of_gt hT]
  have hF_ioc : ∀ x ∈ Ioc (0 : ℝ) T,
      chapter08FUnconditionalTriangle T x =
        (1 - x / T) / Real.cosh (x / 2) := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hratio : |x| / T = x / T := by
      rw [abs_of_pos hxpos]
    have hnonneg : 0 ≤ 1 - x / T := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hT).2 (by simpa using hx.2)
    unfold chapter08FUnconditionalTriangle chapter08TriangularAutocorrelation
    rw [hratio, max_eq_left hnonneg]
  have hF_tail : ∀ x ∈ Ioi T,
      chapter08FUnconditionalTriangle T x = 0 := by
    intro x hx
    have hxpos : 0 < x := lt_trans hT hx
    unfold chapter08FUnconditionalTriangle chapter08TriangularAutocorrelation
    have hratio : 1 < |x| / T := by
      rw [abs_of_pos hxpos]
      apply (lt_div_iff₀ hT).2
      simpa using hx
    rw [max_eq_right (le_of_lt (sub_neg.mpr hratio)), zero_div]
  have hB_ioc_point : ∀ x ∈ Ioc (0 : ℝ) T,
      (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2)) =
        (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2)) + x / (T * Real.sinh x) := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
    rw [hF_ioc x hx]
    rw [hsinh_double x]
    field_simp [ne_of_gt hT, ne_of_gt (Real.cosh_pos (x / 2)),
      ne_of_gt hsinh]
    ring
  have hB_tail_point : ∀ x ∈ Ioi T,
      (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2)) =
        (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2)) + 1 / Real.sinh x := by
    intro x hx
    have hxpos : 0 < x := lt_trans hT hx
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
    rw [hF_tail x hx]
    rw [hsinh_double x]
    field_simp [ne_of_gt (Real.cosh_pos (x / 2)),
      ne_of_gt hsinh]
    ring
  have hB_ioc : IntegrableOn
      (fun x : ℝ => (1 - chapter08FUnconditionalTriangle T x) /
        (2 * Real.sinh (x / 2))) (Ioc 0 T) := by
    apply (hbase_ioc.add hcorr_ioc).congr_fun
    · intro x hx
      exact (hB_ioc_point x hx).symm
    · exact measurableSet_Ioc
  have hB_tail : IntegrableOn
      (fun x : ℝ => (1 - chapter08FUnconditionalTriangle T x) /
        (2 * Real.sinh (x / 2))) (Ioi T) := by
    have hraw : IntegrableOn
        (fun x : ℝ => 1 / (2 * Real.sinh (x / 2))) (Ioi T) := by
      apply (hbase_tail.add htail_data.1).congr_fun
      · intro x hx
        dsimp
        have hxpos : 0 < x := lt_trans hT hx
        have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
        rw [hsinh_double x]
        field_simp [ne_of_gt (Real.cosh_pos (x / 2)),
          ne_of_gt hsinh]
        ring
      · exact measurableSet_Ioi
    apply hraw.congr_fun
    · intro x hx
      dsimp
      rw [hF_tail x hx]
      simp
    · exact measurableSet_Ioi
  have hB_iOi : IntegrableOn
      (fun x : ℝ => (1 - chapter08FUnconditionalTriangle T x) /
        (2 * Real.sinh (x / 2))) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hT.le]
    exact hB_ioc.union hB_tail
  have hB_split := intervalIntegral.integral_interval_add_Ioi
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => (1 - chapter08FUnconditionalTriangle T x) /
      (2 * Real.sinh (x / 2)))
    (a := (0 : ℝ)) (b := T) hB_iOi hB_tail
  rw [intervalIntegral.integral_of_le hT.le] at hB_split
  have hbase_split := intervalIntegral.integral_interval_add_Ioi
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => (1 - 1 / Real.cosh (x / 2)) /
      (2 * Real.sinh (x / 2)))
    (a := (0 : ℝ)) (b := T) hbase_data.1 hbase_tail
  rw [intervalIntegral.integral_of_le hT.le] at hbase_split
  have hcorr_integral :
      (∫ x : ℝ in Ioc 0 T, x / (T * Real.sinh x)) =
        (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) := by
    calc
      (∫ x : ℝ in Ioc 0 T, x / (T * Real.sinh x)) =
          ∫ x : ℝ in Ioc 0 T, (1 / T) * (x / Real.sinh x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        field_simp [ne_of_gt hT]
      _ = (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) := by
        rw [integral_const_mul]
  have hB_ioc_integral :
      (∫ x : ℝ in Ioc 0 T,
        (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) =
        (∫ x : ℝ in Ioc 0 T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) := by
    calc
      (∫ x : ℝ in Ioc 0 T,
        (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) =
          ∫ x : ℝ in Ioc 0 T,
            ((1 - 1 / Real.cosh (x / 2)) /
              (2 * Real.sinh (x / 2)) + x / (T * Real.sinh x)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hB_ioc_point x hx
      _ = (∫ x : ℝ in Ioc 0 T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (∫ x : ℝ in Ioc 0 T, x / (T * Real.sinh x)) := by
        rw [integral_add hbase_ioc hcorr_ioc]
      _ = (∫ x : ℝ in Ioc 0 T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) := by
        rw [hcorr_integral]
  have hB_tail_integral :
      (∫ x : ℝ in Ioi T,
        (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) =
        (∫ x : ℝ in Ioi T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (∫ x : ℝ in Ioi T, 1 / Real.sinh x) := by
    calc
      (∫ x : ℝ in Ioi T,
        (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) =
          ∫ x : ℝ in Ioi T,
            ((1 - 1 / Real.cosh (x / 2)) /
              (2 * Real.sinh (x / 2)) + 1 / Real.sinh x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hB_tail_point x hx
      _ = (∫ x : ℝ in Ioi T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (∫ x : ℝ in Ioi T, 1 / Real.sinh x) := by
        rw [integral_add hbase_tail htail_data.1]
  have hB_decomp : chapter08BT T =
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) /
          (2 * Real.sinh (x / 2))) +
        (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) +
        (∫ x : ℝ in Ioi T, 1 / Real.sinh x) := by
    unfold chapter08BT chapter08B
    calc
      (∫ x : ℝ in Ioi 0,
        (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) =
          (∫ x : ℝ in Ioc 0 T,
            (1 - chapter08FUnconditionalTriangle T x) /
              (2 * Real.sinh (x / 2))) +
            (∫ x : ℝ in Ioi T,
              (1 - chapter08FUnconditionalTriangle T x) /
                (2 * Real.sinh (x / 2))) := hB_split.symm
      _ = ((∫ x : ℝ in Ioc 0 T,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x)) +
          ((∫ x : ℝ in Ioi T,
            (1 - 1 / Real.cosh (x / 2)) /
              (2 * Real.sinh (x / 2))) +
            (∫ x : ℝ in Ioi T, 1 / Real.sinh x)) := by
        rw [hB_ioc_integral, hB_tail_integral]
      _ = (∫ x : ℝ in Ioi 0,
          (1 - 1 / Real.cosh (x / 2)) /
            (2 * Real.sinh (x / 2))) +
          (1 / T) * (∫ x : ℝ in Ioc 0 T, x / Real.sinh x) +
          (∫ x : ℝ in Ioi T, 1 / Real.sinh x) := by
        rw [← hbase_split]
        ring
  rw [hB_decomp, hbase_data.2, hfinite_series, htail_data.2]
  field_simp [ne_of_gt hT]
  ring

theorem chapter08_C_exact_formula {T : ℝ} (hT : 0 < T) :
    chapter08CT T = Real.pi / 2 - (2 / T) * Real.log (Real.cosh (T / 2)) := by
  have hbase_deriv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
      (1 / (2 * Real.cosh (x / 2))) x := by
    intro x hx
    have he := (Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)
    have ha := (Real.hasDerivAt_arctan (Real.exp (x / 2))).comp x he
    have ha' : HasDerivAt (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
        (2 * (1 / (1 + Real.exp (x / 2) ^ 2) *
          (Real.exp (x / 2) * (1 / 2)))) x := by
      simpa only [Function.comp_apply, id_eq] using ha.const_mul 2
    convert ha' using 1
    rw [Real.cosh_eq]
    field_simp [Real.exp_ne_zero]
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    have hxexp : x / 2 + -(x / 2) = 0 := by ring
    rw [hxexp, Real.exp_zero]
    rw [pow_two, ← Real.exp_add]
    ring_nf
  have hbase_pos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ 1 / (2 * Real.cosh (x / 2)) := by
    intro x hx
    positivity
  have hbase_tendsto : Filter.Tendsto
      (fun x : ℝ => 2 * Real.arctan (Real.exp (x / 2)))
      Filter.atTop (nhds Real.pi) := by
    have hscale : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos
        (f := fun x : ℝ => x) (l := Filter.atTop)
        (by norm_num : (0 : ℝ) < 1 / 2)).2 Filter.tendsto_id
    have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (x / 2))
        Filter.atTop Filter.atTop := by
      have h := Real.tendsto_exp_atTop.comp hscale
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
    have harc : Filter.Tendsto
        (fun x : ℝ => Real.arctan (Real.exp (x / 2)))
        Filter.atTop (nhds (Real.pi / 2)) := by
      have h := Real.tendsto_arctan_atTop.comp hexp
      exact tendsto_nhds_of_tendsto_nhdsWithin
        (by simpa [Function.comp_def] using h)
    have hmul := harc.const_mul (2 : ℝ)
    have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [hpi] at hmul
    exact hmul
  have hbase_int : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hbase_deriv hbase_pos hbase_tendsto
  have hbase : (∫ x : ℝ in Ioi 0,
      1 / (2 * Real.cosh (x / 2))) = Real.pi / 2 := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg'
      (g := fun x : ℝ => 2 * Real.arctan (Real.exp (x / 2)))
      (g' := fun x : ℝ => 1 / (2 * Real.cosh (x / 2)))
      (a := (0 : ℝ)) (l := Real.pi) hbase_deriv hbase_pos hbase_tendsto
    convert h using 1
    norm_num [Real.arctan_one]
    ring
  have htanh : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.tanh (y / 2))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
    intro x
    have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_sinh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_cosh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hq := hs.div hc (ne_of_gt (Real.cosh_pos (x / 2)))
    have hfun : (fun y : ℝ => Real.tanh (y / 2)) =
        (fun y : ℝ => Real.sinh (y / 2) / Real.cosh (y / 2)) := by
      funext y
      rw [Real.tanh_eq_sinh_div_cosh]
    rw [hfun]
    apply hq.congr_deriv
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hlog : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.log (Real.cosh (y / 2)))
      (Real.tanh (x / 2) / 2) x := by
    intro x
    have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_cosh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hl := (Real.hasDerivAt_log
      (ne_of_gt (Real.cosh_pos (x / 2)))).comp x hc
    have hfun : (fun y : ℝ => Real.log (Real.cosh (y / 2))) =
        (Real.log ∘ fun y : ℝ => Real.cosh (y / 2)) := by
      funext y
      rfl
    rw [hfun]
    apply hl.congr_deriv
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
  let P : ℝ → ℝ := fun x =>
    (1 - x / T) * Real.tanh (x / 2) +
      (2 / T) * Real.log (Real.cosh (x / 2))
  have hPderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt P
        ((1 - x / T) / (2 * Real.cosh (x / 2) ^ 2)) x := by
    intro x hx
    have hlin : HasDerivAt (fun y : ℝ => 1 - y / T) (-1 / T) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub
          ((hasDerivAt_id x).div_const T) using 1 <;>
        first
        | rfl
        | simp [div_eq_mul_inv]
    have hprod := hlin.mul (htanh x)
    have hlogterm := (hlog x).const_mul (2 / T)
    dsimp [P]
    convert hprod.add hlogterm using 1 <;>
      first
      | rfl
      | simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq]
      | ring
  have hPint : (∫ x : ℝ in (0 : ℝ)..T,
      (1 - x / T) / (2 * Real.cosh (x / 2) ^ 2)) =
      P T - P 0 := by
    have hcont : Continuous (fun x : ℝ =>
        (1 - x / T) / (2 * Real.cosh (x / 2) ^ 2)) := by
      apply (continuous_const.sub (continuous_id.div_const T)).div
      · fun_prop
      · intro x
        positivity
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := T) hPderiv (hcont.intervalIntegrable 0 T)
  have htri_cont : Continuous (chapter08TriangularAutocorrelation T) := by
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hterm_cont : Continuous (fun x : ℝ =>
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2)) := by
    apply htri_cont.div
    · fun_prop
    · intro x
      positivity
  have hterm_compact : HasCompactSupport (fun x : ℝ =>
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2)) := by
    have htri := chapter08_triangular_has_compact_support hT
    rw [hasCompactSupport_iff_eventuallyEq] at htri ⊢
    exact htri.mono (fun x hx => by simp [div_eq_mul_inv, hx])
  have hterm_int : IntegrableOn (fun x : ℝ =>
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2)) (Ioi 0) := by
    exact hterm_cont.integrable_of_hasCompactSupport
      hterm_compact |>.integrableOn
  have hterm_tail_zero : ∀ x ∈ Ioi T,
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2) = 0 := by
    intro x hx
    change T < x at hx
    rw [chapter08TriangularAutocorrelation]
    have hratio : 1 < |x| / T := by
      rw [abs_of_pos (lt_trans hT hx)]
      apply (lt_div_iff₀ hT).2
      linarith
    rw [max_eq_right (le_of_lt (sub_neg.mpr hratio)), zero_div]
  have hterm_Ioi : (∫ x : ℝ in Ioi 0,
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2)) =
      ∫ x : ℝ in (0 : ℝ)..T,
        chapter08TriangularAutocorrelation T x /
          (2 * Real.cosh (x / 2) ^ 2) := by
    have hglobal : Integrable (fun x : ℝ =>
        chapter08TriangularAutocorrelation T x /
          (2 * Real.cosh (x / 2) ^ 2)) :=
      hterm_cont.integrable_of_hasCompactSupport hterm_compact
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2))
      (a := (0 : ℝ)) (b := T) hglobal.integrableOn hglobal.integrableOn
    rw [intervalIntegral.integral_of_le hT.le] at hadd
    have hzero : (∫ x : ℝ in Ioi T,
        chapter08TriangularAutocorrelation T x /
          (2 * Real.cosh (x / 2) ^ 2)) = 0 :=
      integral_eq_zero_of_ae
        (ae_restrict_of_forall_mem measurableSet_Ioi hterm_tail_zero)
    rw [hzero, add_zero] at hadd
    simpa only [intervalIntegral.integral_of_le hT.le] using hadd.symm
  have hpoint : ∀ x : ℝ,
      (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.cosh (x / 2)) =
        1 / (2 * Real.cosh (x / 2)) -
          chapter08TriangularAutocorrelation T x /
            (2 * Real.cosh (x / 2) ^ 2) := by
    intro x
    dsimp [chapter08FUnconditionalTriangle]
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
  have hterm_interval : (∫ x : ℝ in (0 : ℝ)..T,
      chapter08TriangularAutocorrelation T x /
        (2 * Real.cosh (x / 2) ^ 2)) =
      ∫ x : ℝ in (0 : ℝ)..T,
        (1 - x / T) / (2 * Real.cosh (x / 2) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hT.le] at hx
    have hx0 : 0 ≤ x := hx.1
    have hxT : x ≤ T := hx.2
    have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
    change max (1 - |x| / T) 0 /
        (2 * Real.cosh (x / 2) ^ 2) =
      (1 - x / T) / (2 * Real.cosh (x / 2) ^ 2)
    rw [hratio]
    have hlin : 0 ≤ 1 - x / T := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hT).2 (by simpa using hxT)
    rw [max_eq_left hlin]
  unfold chapter08CT chapter08C
  have hsplit : (∫ x : ℝ in Ioi 0,
      (1 - chapter08FUnconditionalTriangle T x) /
        (2 * Real.cosh (x / 2))) =
      (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh (x / 2))) -
        (∫ x : ℝ in Ioi 0,
          chapter08TriangularAutocorrelation T x /
            (2 * Real.cosh (x / 2) ^ 2)) := by
    calc
      (∫ x : ℝ in Ioi 0,
          (1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.cosh (x / 2))) =
          ∫ x : ℝ in Ioi 0,
            (1 / (2 * Real.cosh (x / 2)) -
              chapter08TriangularAutocorrelation T x /
                (2 * Real.cosh (x / 2) ^ 2)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpoint x
      _ = (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh (x / 2))) -
          (∫ x : ℝ in Ioi 0,
            chapter08TriangularAutocorrelation T x /
              (2 * Real.cosh (x / 2) ^ 2)) :=
        integral_sub hbase_int hterm_int
  rw [hsplit, hbase, hterm_Ioi, hterm_interval, hPint]
  simp [P, ne_of_gt hT]

theorem chapter08_B_series_tail_nonnegative
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    0 ≤ chapter08BSeriesTail T m := by
  apply tsum_nonneg
  intro k
  have hodd_pos : 0 < chapter08Odd (m + 1 + k) := by
    dsimp [chapter08Odd]
    positivity
  have hnum : 0 ≤ 1 + chapter08Odd (m + 1 + k) * T := by
    positivity
  exact div_nonneg (mul_nonneg hnum (Real.exp_nonneg _)) (sq_nonneg _)

theorem chapter08_B_series_tail_bound
    {T : ℝ} (hT : 0 < T) (m : ℕ) :
    chapter08BSeriesTail T m ≤
      (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
        (1 - Real.exp (-2 * T)) := by
  let q : ℝ := Real.exp (-2 * T)
  let C : ℝ := (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.exp_nonneg _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : HasSum (fun k : ℕ => q ^ k) (1 - q)⁻¹ :=
    hasSum_geometric_of_lt_one hq0 hq1
  have hmajor : HasSum (fun k : ℕ => C * q ^ k) (C * (1 - q)⁻¹) :=
    hgeom.mul_left C
  have hterm : ∀ k : ℕ,
      chapter08BSeriesTerm T (m + 1 + k) ≤ C * q ^ k := by
    intro k
    have hcoef := chapter08_B_series_coefficient_bound (le_of_lt hT) (m + 1 + k)
    have hexp : Real.exp (-chapter08Odd (m + 1 + k) * T) =
        Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) * q ^ k := by
      dsimp [q, chapter08Odd]
      rw [show -((2 * (m + 1 + k) + 1 : ℕ) : ℝ) * T =
          -((2 * m + 3 : ℕ) : ℝ) * T + (-2 * T) * k by
        push_cast
        ring]
      rw [Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring_nf
    have hodd_pos : 0 < chapter08Odd (m + 1 + k) := by
      dsimp [chapter08Odd]
      positivity
    have hform :
        chapter08BSeriesTerm T (m + 1 + k) =
          ((1 + chapter08Odd (m + 1 + k) * T) /
            (chapter08Odd (m + 1 + k)) ^ 2) *
            (Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) * q ^ k) := by
      rw [chapter08BSeriesTerm, hexp]
      ring
    rw [hform]
    calc
      ((1 + chapter08Odd (m + 1 + k) * T) /
          (chapter08Odd (m + 1 + k)) ^ 2) *
          (Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) * q ^ k) ≤
        (1 + T) * (Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) * q ^ k) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = C * q ^ k := by simp [C]; ring
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ chapter08BSeriesTerm T (m + 1 + k) := by
    intro k
    rw [chapter08BSeriesTerm]
    have hodd_pos : 0 < chapter08Odd (m + 1 + k) := by
      dsimp [chapter08Odd]
      positivity
    exact div_nonneg (mul_nonneg (by nlinarith) (Real.exp_nonneg _)) (sq_nonneg _)
  have hsumterm : Summable (fun k : ℕ => chapter08BSeriesTerm T (m + 1 + k)) := by
    apply Summable.of_norm_bounded_eventually_nat (hmajor.summable)
    filter_upwards [] with k
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg k)]
    exact hterm k
  unfold chapter08BSeriesTail
  calc
    (∑' k : ℕ, chapter08BSeriesTerm T (m + 1 + k)) ≤
        ∑' k : ℕ, C * q ^ k := hsumterm.tsum_le_tsum hterm hmajor.summable
    _ = C * (1 - q)⁻¹ := hmajor.tsum_eq
    _ = (1 + T) * Real.exp (-((2 * m + 3 : ℕ) : ℝ) * T) /
          (1 - Real.exp (-2 * T)) := by
      dsimp [C, q]
      rw [div_eq_mul_inv]

theorem chapter08_limiting_archimedean_integrals :
    (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) =
        Real.log 2 ∧
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.cosh (x / 2))) =
        Real.pi / 2 - 1 := by
  have hscale : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos
      (f := fun x : ℝ => x) (l := Filter.atTop)
      (by norm_num : (0 : ℝ) < 1 / 2)).2 Filter.tendsto_id
  have hexp_neg : Filter.Tendsto (fun x : ℝ => Real.exp (-x))
      Filter.atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hbase_deriv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
      (1 / (2 * Real.cosh (x / 2))) x := by
    intro x hx
    have he := (Real.hasDerivAt_exp (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)
    have ha := (Real.hasDerivAt_arctan (Real.exp (x / 2))).comp x he
    have ha' : HasDerivAt (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)))
        (2 * (1 / (1 + Real.exp (x / 2) ^ 2) *
          (Real.exp (x / 2) * (1 / 2)))) x := by
      simpa only [Function.comp_apply, id_eq] using ha.const_mul 2
    convert ha' using 1
    rw [Real.cosh_eq]
    field_simp [Real.exp_ne_zero]
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    have hxexp : x / 2 + -(x / 2) = 0 := by ring
    rw [hxexp, Real.exp_zero]
    rw [pow_two, ← Real.exp_add]
    ring_nf
  have hbase_pos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ 1 / (2 * Real.cosh (x / 2)) := by
    intro x hx
    positivity
  have hbase_tendsto : Filter.Tendsto
      (fun x : ℝ => 2 * Real.arctan (Real.exp (x / 2)))
      Filter.atTop (nhds Real.pi) := by
    have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (x / 2))
        Filter.atTop Filter.atTop := by
      have h := Real.tendsto_exp_atTop.comp hscale
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
    have harc : Filter.Tendsto
        (fun x : ℝ => Real.arctan (Real.exp (x / 2)))
        Filter.atTop (nhds (Real.pi / 2)) := by
      have h := Real.tendsto_arctan_atTop.comp hexp
      exact tendsto_nhds_of_tendsto_nhdsWithin
        (by simpa [Function.comp_def] using h)
    have hmul := harc.const_mul (2 : ℝ)
    have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [hpi] at hmul
    exact hmul
  have htanh_deriv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Real.tanh (y / 2))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
    intro x
    have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
        (Real.cosh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_sinh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
        (Real.sinh (x / 2) / 2) x := by
      simpa [Function.comp_def, div_eq_mul_inv] using
        (Real.hasDerivAt_cosh (x / 2)).comp x
          ((hasDerivAt_id x).div_const 2)
    have hq := hs.div hc (ne_of_gt (Real.cosh_pos (x / 2)))
    have hfun : (fun y : ℝ => Real.tanh (y / 2)) =
        (fun y : ℝ => Real.sinh (y / 2) / Real.cosh (y / 2)) := by
      funext y
      rw [Real.tanh_eq_sinh_div_cosh]
    rw [hfun]
    apply hq.congr_deriv
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have htanh_formula : ∀ z : ℝ,
      Real.tanh z = (1 - Real.exp (-2 * z)) / (1 + Real.exp (-2 * z)) := by
    intro z
    rw [Real.tanh_eq]
    have hprod : Real.exp z * Real.exp (-z) = 1 := by
      rw [← Real.exp_add]
      simp
    have hsq : Real.exp (-2 * z) = Real.exp (-z) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
    have ha : Real.exp z = 1 / Real.exp (-z) := by
      apply (eq_div_iff (Real.exp_ne_zero _)).2
      simpa using hprod
    have hden₁ : Real.exp z + Real.exp (-z) ≠ 0 := by positivity
    have hden₂ : 1 + Real.exp (-z) ^ 2 ≠ 0 := by positivity
    rw [ha]
    field_simp [hden₁, hden₂, Real.exp_ne_zero]
  have htanh_tendsto : Filter.Tendsto
      (fun x : ℝ => Real.tanh (x / 2)) Filter.atTop (nhds 1) := by
    have hcont : ContinuousAt (fun y : ℝ => (1 - y) / (1 + y)) 0 := by
      have hnum : ContinuousAt (fun y : ℝ => 1 - y) 0 :=
        (continuous_const.sub continuous_id).continuousAt
      have hden : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact hnum.div₀ hden (by norm_num)
    have h := hcont.tendsto.comp hexp_neg
    have h' : Filter.Tendsto
        (fun x : ℝ => (1 - Real.exp (-x)) / (1 + Real.exp (-x)))
        Filter.atTop (nhds 1) := by
      convert h using 1 <;> simp [Function.comp_def]
    have heq : ∀ x : ℝ, Real.tanh (x / 2) =
        (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
      intro x
      rw [htanh_formula]
      have harg : -2 * (x / 2) = -x := by ring
      rw [harg]
    simpa [heq] using h'
  have hQderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => Real.log (1 + Real.exp (-y)) -
        2 * Real.log (1 + Real.exp (-(y / 2))))
      ((1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) x := by
    intro x hx
    have harg₁ : HasDerivAt (fun y : ℝ => 1 + Real.exp (-y))
        (-Real.exp (-x)) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add
          ((Real.hasDerivAt_exp (-x)).comp x
            ((hasDerivAt_id x).neg)) using 1
      all_goals first | rfl | ring
    have hlog₁ : HasDerivAt (fun y : ℝ => Real.log (1 + Real.exp (-y)))
        (-Real.exp (-x) / (1 + Real.exp (-x))) x := by
      have hl := (Real.hasDerivAt_log (by positivity :
        1 + Real.exp (-x) ≠ 0)).comp x harg₁
      have hfun : (fun y : ℝ => Real.log (1 + Real.exp (-y))) =
          (Real.log ∘ fun y : ℝ => 1 + Real.exp (-y)) := by
        funext y
        rfl
      rw [hfun]
      apply hl.congr_deriv
      field_simp
    have harg₂ : HasDerivAt (fun y : ℝ => 1 + Real.exp (-(y / 2)))
        (-Real.exp (-(x / 2)) / 2) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add
          ((Real.hasDerivAt_exp (-(x / 2))).comp x
            ((hasDerivAt_id x).div_const 2 |>.neg)) using 1
      all_goals first | rfl | ring
    have hlog₂ : HasDerivAt
        (fun y : ℝ => Real.log (1 + Real.exp (-(y / 2))))
        ((-Real.exp (-(x / 2)) / 2) / (1 + Real.exp (-(x / 2)))) x := by
      have hl := (Real.hasDerivAt_log (by positivity :
        1 + Real.exp (-(x / 2)) ≠ 0)).comp x harg₂
      have hfun : (fun y : ℝ => Real.log (1 + Real.exp (-(y / 2)))) =
          (Real.log ∘ fun y : ℝ => 1 + Real.exp (-(y / 2))) := by
        funext y
        rfl
      rw [hfun]
      apply hl.congr_deriv
      field_simp
    have hsub := hlog₁.sub (hlog₂.const_mul 2)
    convert hsub using 1 <;>
      first
      | rfl
      | simp only [Pi.sub_apply, Pi.const_mul_apply, Function.comp_apply, id_eq]
      | by_cases hx0 : x = 0
        · subst x
          norm_num [Real.cosh_zero, Real.sinh_zero, Real.exp_zero]
        · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
          have hdiff : Real.exp (x / 2) - Real.exp (-(x / 2)) ≠ 0 := by
            apply ne_of_gt
            apply sub_pos.mpr
            exact Real.exp_lt_exp.mpr (by linarith)
          rw [Real.cosh_eq, Real.sinh_eq]
          field_simp [Real.exp_ne_zero, hdiff]
          have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
            rw [← Real.exp_add]
            simp
          have hsq : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
          have ha : Real.exp (x / 2) = 1 / Real.exp (-(x / 2)) := by
            apply (eq_div_iff (Real.exp_ne_zero _)).2
            simpa using hprod
          rw [hsq, ha]
          field_simp [Real.exp_ne_zero, hdiff]
          ring
  have hQpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)) := by
    intro x hx
    have hxpos : 0 < x := hx
    have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
    have hinv : 1 / Real.cosh (x / 2) ≤ 1 := by
      rw [div_le_iff₀ (Real.cosh_pos _)]
      nlinarith
    have hsinh : 0 < Real.sinh (x / 2) := by
      rw [Real.sinh_pos_iff]
      linarith
    exact div_nonneg (sub_nonneg.mpr hinv) (by positivity)
  have hQ_tendsto : Filter.Tendsto
      (fun x : ℝ => Real.log (1 + Real.exp (-x)) -
        2 * Real.log (1 + Real.exp (-(x / 2))))
      Filter.atTop (nhds 0) := by
    have hlogcont : ContinuousAt (fun y : ℝ => Real.log (1 + y)) 0 := by
      have harg : ContinuousAt (fun y : ℝ => 1 + y) 0 :=
        (continuous_const.add continuous_id).continuousAt
      exact harg.log (by norm_num)
    have h₁ := hlogcont.tendsto.comp hexp_neg
    have hneg_half : Filter.Tendsto (fun x : ℝ => Real.exp (-(x / 2)))
        Filter.atTop (nhds 0) := by
      have h := hexp_neg.comp hscale
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using h
    have h₂ := hlogcont.tendsto.comp hneg_half
    have h₁' : Filter.Tendsto (fun x : ℝ => Real.log (1 + Real.exp (-x)))
        Filter.atTop (nhds 0) := by
      convert h₁ using 1 <;> simp [Function.comp_def]
    have h₂' : Filter.Tendsto
        (fun x : ℝ => Real.log (1 + Real.exp (-(x / 2))))
        Filter.atTop (nhds 0) := by
      convert h₂ using 1 <;> simp [Function.comp_def]
    simpa using h₁'.sub (h₂'.const_mul 2)
  have hQint := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun x : ℝ => Real.log (1 + Real.exp (-x)) -
      2 * Real.log (1 + Real.exp (-(x / 2))))
    (g' := fun x : ℝ =>
      (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2)))
    (a := (0 : ℝ)) (l := (0 : ℝ)) hQderiv hQpos hQ_tendsto
  have hQzero :
      (Real.log (1 + Real.exp (-(0 : ℝ))) -
        2 * Real.log (1 + Real.exp (-((0 : ℝ) / 2)))) = -Real.log 2 := by
    norm_num [Real.exp_zero]
    ring
  have hBlim :
      (∫ x : ℝ in Ioi 0,
        (1 - 1 / Real.cosh (x / 2)) / (2 * Real.sinh (x / 2))) =
        Real.log 2 := by
    rw [hQint, hQzero]
    ring
  have hPderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => 2 * Real.arctan (Real.exp (y / 2)) - Real.tanh (y / 2))
      ((1 - 1 / Real.cosh (x / 2)) / (2 * Real.cosh (x / 2))) x := by
    intro x hx
    have hsub := (hbase_deriv x hx).sub (htanh_deriv x)
    convert hsub using 1 <;>
      first
      | rfl
      | simp only [Pi.sub_apply, Function.comp_apply, id_eq]
      | field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
  have hPpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ (1 - 1 / Real.cosh (x / 2)) / (2 * Real.cosh (x / 2)) := by
    intro x hx
    have hcosh : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
    have hinv : 1 / Real.cosh (x / 2) ≤ 1 := by
      rw [div_le_iff₀ (Real.cosh_pos _)]
      nlinarith
    exact div_nonneg (sub_nonneg.mpr hinv) (by positivity)
  have hP_tendsto : Filter.Tendsto
      (fun x : ℝ => 2 * Real.arctan (Real.exp (x / 2)) - Real.tanh (x / 2))
      Filter.atTop (nhds (Real.pi - 1)) := by
    have h := hbase_tendsto.sub htanh_tendsto
    simpa using h
  have hPint := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun x : ℝ =>
      2 * Real.arctan (Real.exp (x / 2)) - Real.tanh (x / 2))
    (g' := fun x : ℝ =>
      (1 - 1 / Real.cosh (x / 2)) / (2 * Real.cosh (x / 2)))
    (a := (0 : ℝ)) (l := Real.pi - 1) hPderiv hPpos hP_tendsto
  have hPzero :
      2 * Real.arctan (Real.exp ((0 : ℝ) / 2)) - Real.tanh ((0 : ℝ) / 2) =
        Real.pi / 2 := by
    norm_num [Real.exp_zero, Real.arctan_one, Real.tanh_zero]
    ring
  constructor
  · exact hBlim
  · rw [hPint, hPzero]
    ring

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
