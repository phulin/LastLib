import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Section01StatementWithEveryTermVisible
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology Filter
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

/-! ### 6.4. Gamma and pole terms -/

theorem chapter06_gamma_arguments_positive_on_right_line
    {c t : ℝ} (hc : 1 < c) :
    0 < (chapter06VerticalLinePoint c t).re ∧
      0 < (chapter06VerticalLinePoint c t / 2).re := by
  simp [chapter06VerticalLinePoint]
  linarith

theorem chapter06_digamma_integral_applicable_on_right_line
    {c t : ℝ} (hc : 1 < c) :
    0 < (chapter06VerticalLinePoint c t).re ∧
      0 < (chapter06VerticalLinePoint c t / 2).re := by
  exact chapter06_gamma_arguments_positive_on_right_line hc

def chapter06DigammaIntegralIntegrand (z : ℂ) (x : ℝ) : ℂ :=
  (((Real.exp (-x) : ℝ) : ℂ) - Complex.exp (-(z * (x : ℂ)))) /
    (1 - (Real.exp (-x) : ℂ))

def chapter06DigammaSeriesTerm (z : ℂ) (k : ℕ) : ℂ :=
  (1 / ((k + 1 : ℕ) : ℂ)) - 1 / ((k : ℂ) + z)

theorem chapter06_digamma_eq_gamma_log_derivative (z : ℂ) :
    Complex.digamma z = chapter06LogDerivative Complex.Gamma z := by
  rfl

theorem chapter06_digamma_series_representation
    {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      (-Real.eulerMascheroniConstant : ℂ) +
        ∑' k : ℕ, chapter06DigammaSeriesTerm z k := by
  sorry

theorem chapter06_digamma_series_absolutely_summable
    {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℕ => ‖chapter06DigammaSeriesTerm z k‖) := by
  let a : ℝ := min z.re 1
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min hz (by norm_num)
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa [abs_of_nonneg, pow_two] using
      ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))
  have hsC :
      Summable (fun k : ℕ => (‖z - 1‖ / a) * (1 / ((k : ℝ) + 1) ^ 2)) :=
    hs.mul_left (‖z - 1‖ / a)
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hsC
  intro k
  have hkz : (k : ℂ) + z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith [show 0 ≤ (k : ℝ) by positivity]
  have hrewrite :
      chapter06DigammaSeriesTerm z k =
        (z - 1) / (((k + 1 : ℕ) : ℂ) * ((k : ℂ) + z)) := by
    dsimp [chapter06DigammaSeriesTerm]
    field_simp [hkz]
    norm_num [Nat.cast_add, Nat.cast_one]
  have hklower : a * ((k : ℝ) + 1) ≤ (k : ℝ) + z.re := by
    have hka : a ≤ z.re := by
      dsimp [a]
      exact min_le_left _ _
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact min_le_right _ _
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    nlinarith [mul_nonneg hk0 (sub_nonneg.mpr ha1)]
  have hden : a * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + z‖ := by
    calc
      a * ((k : ℝ) + 1) ≤ (k : ℝ) + z.re := hklower
      _ = ((k : ℂ) + z).re := by simp
      _ ≤ ‖(k : ℂ) + z‖ := Complex.re_le_norm _
  have hden2 :
      a * ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + z‖ := by
    calc
      a * ((k : ℝ) + 1) ^ 2 = ((k : ℝ) + 1) * (a * ((k : ℝ) + 1)) := by ring
      _ ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + z‖ :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  have hLpos : 0 < a * ((k : ℝ) + 1) ^ 2 := by
    positivity
  calc
    ‖chapter06DigammaSeriesTerm z k‖ =
        ‖z - 1‖ / (((k : ℝ) + 1) * ‖(k : ℂ) + z‖) := by
      rw [hrewrite, norm_div, norm_mul]
      rw [Complex.norm_natCast]
      norm_num
    _ ≤ ‖z - 1‖ / (a * ((k : ℝ) + 1) ^ 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hLpos hden2
    _ = (‖z - 1‖ / a) * (1 / ((k : ℝ) + 1) ^ 2) := by
      field_simp [ne_of_gt ha]

theorem chapter06_digamma_integral_representation
    {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      (-Real.eulerMascheroniConstant : ℂ) +
        ∫ x : ℝ in Ioi 0, chapter06DigammaIntegralIntegrand z x := by
  sorry

theorem chapter06_digamma_integrand_integrable
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (chapter06DigammaIntegralIntegrand z) (Ioi 0) := by
  let N : ℝ → ℂ := fun x =>
    ((Real.exp (-x) : ℝ) : ℂ) - Complex.exp (-(z * (x : ℂ)))
  let D : ℝ → ℝ := fun x => 1 - Real.exp (-x)
  let Q : ℝ → ℂ := fun x => N x / (D x : ℂ)
  have hN0 : N 0 = 0 := by
    simp [N]
  have hD0 : D 0 = 0 := by
    simp [D]
  have hN : Continuous N := by
    dsimp [N]
    fun_prop
  have hD : Continuous D := by
    dsimp [D]
    fun_prop
  have hNderiv : HasDerivAt N (z - 1) 0 := by
    have hreal : HasDerivAt (fun x : ℝ =>
        ((Real.exp (-x) : ℝ) : ℂ)) (-1 : ℂ) 0 := by
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1 : ℝ) 0 := by
        convert! ((Real.hasDerivAt_exp (0 : ℝ)).comp_of_eq (0 : ℝ)
          (hasDerivAt_neg' (0 : ℝ)) (by simp)) using 1; norm_num
      convert hexp.ofReal_comp using 1; norm_num
    have harg : HasDerivAt (fun x : ℝ => -(z * (x : ℂ))) (-z) 0 := by
      convert! ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul z).neg using 1
        ; simp
    have hcomplex : HasDerivAt (fun x : ℝ =>
        Complex.exp (-(z * (x : ℂ)))) (-z) 0 := by
      convert! ((Complex.hasDerivAt_exp (0 : ℂ)).scomp_of_eq (0 : ℝ) harg (by simp)) using 1
        ; simp
    dsimp [N]
    convert! hreal.sub hcomplex using 1; simp; ring
  have hDderiv : HasDerivAt D 1 0 := by
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1 : ℝ) 0 := by
      convert! ((Real.hasDerivAt_exp (0 : ℝ)).comp_of_eq (0 : ℝ)
        (hasDerivAt_neg' (0 : ℝ)) (by simp)) using 1; norm_num
    dsimp [D]
    convert! (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp using 1
      ; simp
  have hNslope : Tendsto (dslope N 0) (𝓝 0) (𝓝 (z - 1)) := by
    convert (continuousAt_dslope_same.mpr hNderiv.differentiableAt).tendsto using 1
    simp [hNderiv.deriv]
  have hDslope : Tendsto (dslope D 0) (𝓝 0) (𝓝 (1 : ℝ)) := by
    convert (continuousAt_dslope_same.mpr hDderiv.differentiableAt).tendsto using 1
    simp [hDderiv.deriv]
  have hDslopeC : Tendsto (fun x : ℝ => ((dslope D 0 x : ℝ) : ℂ))
      (𝓝 0) (𝓝 (1 : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.continuous.tendsto (1 : ℝ)).comp hDslope
  have hratio : Tendsto (fun x : ℝ =>
      dslope N 0 x / ((dslope D 0 x : ℝ) : ℂ)) (𝓝 0) (𝓝 (z - 1)) := by
    change Tendsto (dslope N 0 / (fun x : ℝ => ((dslope D 0 x : ℝ) : ℂ)))
      (𝓝 0) (𝓝 (z - 1))
    simpa [div_one] using hNslope.div hDslopeC (by norm_num : (1 : ℂ) ≠ 0)
  have hfactorN : ∀ {x : ℝ}, x ≠ 0 →
      N x = (x : ℂ) * dslope N 0 x := by
    intro x hx
    have h := sub_smul_dslope N 0 x
    rw [hN0] at h
    simpa [Complex.real_smul, sub_zero] using h.symm
  have hfactorD : ∀ {x : ℝ}, x ≠ 0 →
      D x = x * dslope D 0 x := by
    intro x hx
    have h := sub_smul_dslope D 0 x
    rw [hD0] at h
    simpa [sub_zero] using h.symm
  have hDne : ∀ᶠ x : ℝ in 𝓝[>] 0, dslope D 0 x ≠ 0 := by
    filter_upwards [(hDslope.eventually
      (Ioi_mem_nhds (show (1 : ℝ) ∈ Ioi (1 / 2) by norm_num))).filter_mono
        nhdsWithin_le_nhds] with x hx
    exact ne_of_gt (by linarith)
  have hquot_eq : (fun x : ℝ => Q x) =ᶠ[𝓝[>] 0]
      (fun x : ℝ => dslope N 0 x / ((dslope D 0 x : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin, hDne] with x hx hdx
    have hx0 : x ≠ 0 := ne_of_gt hx
    change N x / (D x : ℂ) = _
    rw [hfactorN hx0, hfactorD hx0]
    push_cast
    field_simp [hx0, Complex.ofReal_ne_zero.mpr hx0, hdx]
  have hQlimit : Tendsto Q (𝓝[>] 0) (𝓝 (z - 1)) := by
    apply (hratio.mono_left nhdsWithin_le_nhds).congr'
    exact hquot_eq.symm
  have hQmeas : AEStronglyMeasurable Q volume := by
    apply (hN.measurable.div
      (Complex.continuous_ofReal.comp hD).measurable).aestronglyMeasurable
  obtain ⟨M, hM⟩ := hQlimit.norm.isBoundedUnder_le
  have hM' : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioi (0 : ℝ) → ‖Q x‖ ≤ M :=
    eventually_nhdsWithin_iff.mp hM
  obtain ⟨ε, hε, hMε⟩ := Metric.eventually_nhds_iff.mp hM'
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact (min_le_right _ _).trans (by norm_num)
  have hnear : IntegrableOn Q (Ioc 0 δ) := by
    apply Measure.integrableOn_of_bounded (μ := volume)
      (s := Ioc (0 : ℝ) δ) measure_Ioc_lt_top.ne hQmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxpos : 0 < x := hx.1
    have hdist : dist x 0 < ε := by
      simp only [Real.dist_eq, sub_zero, abs_of_pos hxpos]
      have hxδ : x ≤ δ := hx.2
      have hδε : δ ≤ ε / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      have hxε : x ≤ ε / 2 := hxδ.trans hδε
      linarith
    exact hMε hdist hxpos
  have hDpos : ∀ {x : ℝ}, 0 < x → 0 < D x := by
    intro x hx
    dsimp [D]
    have hlt : Real.exp (-x) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hmid_cont : ContinuousOn Q (Icc δ 1) := by
    apply hN.continuousOn.div (Complex.continuous_ofReal.comp hD).continuousOn
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (hDpos (lt_of_lt_of_le hδ hx.1)).ne'
  have hmid : IntegrableOn Q (Icc δ 1) := hmid_cont.integrableOn_Icc
  have hNtail : IntegrableOn N (Ioi 1) := by
    have h₁ : IntegrableOn (fun x : ℝ =>
        ((Real.exp (-x) : ℝ) : ℂ)) (Ioi 1) := by
      exact Complex.ofRealCLM.integrable_comp (integrableOn_exp_neg_Ioi 1)
    have h₂ : IntegrableOn (fun x : ℝ =>
        Complex.exp ((-z) * (x : ℂ))) (Ioi 1) := by
      apply integrableOn_exp_mul_complex_Ioi
      change -z.re < 0
      linarith
    dsimp [N]
    convert h₁.sub h₂ using 1
    funext x
    simp [neg_mul]
  let d : ℝ := D 1
  have hd : 0 < d := hDpos (by norm_num)
  have hDlower : ∀ {x : ℝ}, x ∈ Ioi (1 : ℝ) → d ≤ D x := by
    intro x hx
    have hx' : 1 < x := hx
    dsimp [d, D]
    have hexp : Real.exp (-x) ≤ Real.exp (-1) := by
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hQtail : IntegrableOn Q (Ioi 1) := by
    have hmajor : IntegrableOn (fun x : ℝ =>
        (1 / d) * ‖N x‖) (Ioi 1) := hNtail.norm.const_mul _
    apply Integrable.mono' hmajor
    · exact hQmeas.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change ‖N x / (D x : ℂ)‖ ≤ _
      rw [norm_div, Complex.norm_real]
      have hDx : 0 < D x := hDpos (lt_trans (by norm_num) hx)
      simp only [Real.norm_eq_abs, abs_of_pos hDx]
      calc
        ‖N x‖ / D x ≤ ‖N x‖ / d := by
          exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hDlower hx)
        _ = (1 / d) * ‖N x‖ := by ring
  have h01 : IntegrableOn Q (Ioc 0 1) := by
    apply (hnear.union hmid).mono_set
    intro x hx
    by_cases hxd : x ≤ δ
    · exact Or.inl ⟨hx.1, hxd⟩
    · exact Or.inr ⟨le_of_not_ge hxd, hx.2⟩
  have hall : IntegrableOn Q (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact h01.union hQtail
  have hfunc : chapter06DigammaIntegralIntegrand z = Q := by
    funext x
    simp [chapter06DigammaIntegralIntegrand, Q, N, D]
  rw [hfunc]
  exact hall

theorem chapter06_real_place_contribution_formula
    (F : ℝ → ℝ) :
    chapter06RealPlaceContribution F =
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2 -
        (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))) -
        (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))) := by
  rfl

theorem chapter06_complex_place_contribution_formula
    (F : ℝ → ℝ) :
    chapter06ComplexPlaceContribution F =
      2 * (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) -
        2 * ∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2)) := by
  rfl

theorem chapter06_gamma_place_contributions_sum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) :
    (chapter06RealPlaces K : ℝ) * chapter06RealPlaceContribution F +
        (chapter06ComplexPlaces K : ℝ) * chapter06ComplexPlaceContribution F =
      (chapter06Degree K : ℝ) * (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F := by
  rw [chapter06_real_place_contribution_formula,
    chapter06_complex_place_contribution_formula]
  have hB :
      (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.sinh (x / 2))) =
        chapter06B F := rfl
  have hC :
      (∫ x : ℝ in Ioi 0, (1 - F x) / (2 * Real.cosh (x / 2))) =
        chapter06C F := rfl
  rw [hB, hC, ← chapter06_signature_degree (K := K)]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

theorem chapter06_integral_two_cosh_half :
    (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh (x / 2))) = Real.pi / 2 := by
  have hscale :
      (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh (x / 2))) =
        2 * ∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh x) := by
    have h := integral_comp_mul_left_Ioi
      (g := fun x : ℝ => 1 / (2 * Real.cosh x)) 0
      (b := (1 / 2 : ℝ)) (by norm_num)
    simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hsub :
      (∫ x : ℝ in Ioi 0, 1 / (2 * Real.cosh x)) =
        ∫ y : ℝ in Ioi 1, (1 + y ^ 2)⁻¹ := by
    have h := integral_comp_exp_Ioi
      (g := fun y : ℝ => (1 + y ^ 2)⁻¹) 0
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul, Real.cosh_eq]
    field_simp [Real.exp_ne_zero]
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [mul_add, hprod]
    ring
    · norm_num
  rw [hscale, hsub, integral_Ioi_inv_one_add_sq]
  rw [Real.arctan_one]
  ring

theorem chapter06_phi_at_zero_and_one
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    chapter06Phi F 0 =
        (2 * chapter06A F : ℂ) ∧
      chapter06Phi F 1 = (2 * chapter06A F : ℂ) := by
  have hInt : ∀ s : ℂ,
      Integrable (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x) volume :=
    fun s => chapter05_basically_admissible_laplace_integrable hF s
  have hsymm : chapter06Phi F 0 = chapter06Phi F 1 := by
    unfold chapter06Phi
    simpa using chapter05_laplace_reflection hF.even hInt 0
  let gminus : ℝ → ℂ := fun x =>
    (F x : ℂ) * chapter05LaplaceKernel 0 x
  let gplus : ℝ → ℂ := fun x =>
    (F x : ℂ) * chapter05LaplaceKernel 1 x
  have hgminus : Integrable gminus := by
    simpa [gminus] using hInt 0
  have hgplus : Integrable gplus := by
    simpa [gplus] using hInt 1
  have hneg : (∫ x in Iic (0 : ℝ), gminus x) =
      ∫ x in Ioi (0 : ℝ), gplus x := by
    have hchange := (integral_comp_neg_Ioi (E := ℂ) 0 gminus).symm
    rw [neg_zero] at hchange
    convert hchange using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [gminus, gplus, chapter05LaplaceKernel]
    rw [hF.even x]
    ring_nf
  have hsplit : (∫ x : ℝ, gminus x) =
      (∫ x : ℝ in Ioi 0, gminus x) +
        ∫ x : ℝ in Iic 0, gminus x := by
    simpa [compl_Ioi] using (integral_add_compl measurableSet_Ioi hgminus).symm
  have hsum : (∫ x : ℝ in Ioi 0, gminus x) +
      ∫ x : ℝ in Ioi 0, gplus x =
      ∫ x : ℝ in Ioi 0, (gminus x + gplus x) := by
    exact (integral_add hgminus.integrableOn hgplus.integrableOn).symm
  have hphi0 : chapter06Phi F 0 =
      (2 * chapter06A F : ℂ) := by
    change ∫ x : ℝ, gminus x = (2 * chapter06A F : ℂ)
    have hrew : (∫ x : ℝ, gminus x) =
        (∫ x : ℝ in Ioi 0, gminus x) +
          ∫ x : ℝ in Ioi 0, gplus x := by
      rw [hsplit, hneg]
    rw [hrew, hsum]
    have hinterm : (fun x : ℝ => gminus x + gplus x) =
        (fun x : ℝ => ((2 * F x * Real.cosh (x / 2) : ℝ) : ℂ)) := by
      funext x
      simp [gminus, gplus, chapter05LaplaceKernel, Real.cosh_eq]
      ring_nf
    rw [hinterm]
    have hreal :
        (∫ x : ℝ in Ioi 0,
            ((2 * F x * Real.cosh (x / 2) : ℝ) : ℂ)) =
          (2 * chapter06A F : ℂ) := by
      have hcast := (integral_ofReal (𝕜 := ℂ)
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x : ℝ => 2 * F x * Real.cosh (x / 2)))
      have hscalar :
          (∫ x : ℝ in Ioi 0, 2 * F x * Real.cosh (x / 2)) =
            2 * ∫ x : ℝ in Ioi 0, F x * Real.cosh (x / 2) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      calc
        (∫ x : ℝ in Ioi 0,
            ((2 * F x * Real.cosh (x / 2) : ℝ) : ℂ)) =
            ((∫ x : ℝ in Ioi 0, 2 * F x * Real.cosh (x / 2) : ℝ) : ℂ) := hcast
        _ = ((2 * ∫ x : ℝ in Ioi 0, F x * Real.cosh (x / 2) : ℝ) : ℂ) :=
          congrArg (fun r : ℝ => (r : ℂ)) hscalar
        _ = (2 * chapter06A F : ℂ) := by simp [chapter06A]
    exact hreal
  exact ⟨hphi0, hsymm.symm.trans hphi0⟩

def chapter06PoleFactorTransformContribution (F : ℝ → ℝ) : ℝ :=
  -(chapter06Phi F 0 + chapter06Phi F 1).re

theorem chapter06_pole_factor_transform_contribution
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    chapter06PoleFactorTransformContribution F = -4 * chapter06A F := by
  unfold chapter06PoleFactorTransformContribution
  rw [(chapter06_phi_at_zero_and_one hF).1,
    (chapter06_phi_at_zero_and_one hF).2]
  norm_num
  ring

theorem chapter06_pole_terms_enter_with_negative_sign
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F)
    (hFnonnegative : ∀ x, 0 ≤ F x) :
    chapter06PoleFactorTransformContribution F ≤ 0 := by
  rw [chapter06_pole_factor_transform_contribution hF]
  have hA : 0 ≤ chapter06A F := by
    unfold chapter06A
    apply integral_nonneg
    intro x
    exact mul_nonneg (hFnonnegative x) (Real.cosh_pos _).le
  linarith

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
