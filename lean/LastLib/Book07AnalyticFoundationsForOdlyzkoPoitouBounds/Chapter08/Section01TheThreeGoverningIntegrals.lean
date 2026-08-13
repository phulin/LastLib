import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ## 8.1 The three governing integrals -/

variable {K : Type*} [Field K] [NumberField K]

theorem chapter08_signature_formula :
    Chapter08RealPlaceCount K + 2 * Chapter08ComplexPlaceCount K = Chapter08Degree K := by
  exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

theorem chapter08_signature_proportion_nonnegative (hK : 0 < Chapter08Degree K) :
    0 ≤ chapter08SignatureProportion K := by
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (Nat.cast_pos.mpr hK))

theorem chapter08_signature_proportion_le_one (hK : 0 < Chapter08Degree K) :
    chapter08SignatureProportion K ≤ 1 := by
  rw [chapter08SignatureProportion, div_le_iff₀ (Nat.cast_pos.mpr hK)]
  have hsig := chapter08_signature_formula (K := K)
  have hsig' : (Chapter08RealPlaceCount K : ℝ) +
      2 * (Chapter08ComplexPlaceCount K : ℝ) = (Chapter08Degree K : ℝ) := by
    exact_mod_cast hsig
  have hcomplex : 0 ≤ (Chapter08ComplexPlaceCount K : ℝ) := by positivity
  nlinarith

theorem chapter08_absolute_discriminant_pos (hK : 0 < Chapter08Degree K) :
    0 < Chapter08AbsoluteDiscriminant K := by
  unfold Chapter08AbsoluteDiscriminant
  have hd : 0 < (Chapter08Degree K : ℝ) := Nat.cast_pos.mpr hK
  have hprod : 0 < |(NumberField.discr K : ℝ)| * (Chapter08Degree K : ℝ) :=
    mul_pos (abs_pos.mpr (by exact_mod_cast (NumberField.discr_ne_zero K))) hd
  nlinarith

theorem chapter08_archimedean_integrals_convergent
    {F : ℝ → ℝ} (hF : Chapter08BasicallyAdmissible F) :
    IntegrableOn (fun x : ℝ => F x * Real.cosh (x / 2)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2))) (Ioi 0) := by
  rcases hF with ⟨heven, hcont, hcompact, hpiece, hderiv, hF0, hnear⟩
  have hAcont : Continuous (fun x : ℝ => F x * Real.cosh (x / 2)) := by
    fun_prop
  have hAcompact : HasCompactSupport (fun x : ℝ => F x * Real.cosh (x / 2)) := by
    change HasCompactSupport (F * fun x : ℝ => Real.cosh (x / 2))
    exact hcompact.mul_right
  have hA : IntegrableOn (fun x : ℝ => F x * Real.cosh (x / 2)) (Ioi 0) :=
    (hAcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hAcompact).integrableOn
  have hBsmall : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioc 0 1) := by
    show Integrable (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2)))
      (volume.restrict (Ioc 0 1))
    apply hnear.integrable.mono'
    · exact ((measurable_const.sub hcont.measurable).div
        (measurable_const.mul
          (Real.continuous_sinh.measurable.comp
            (measurable_id.div measurable_const)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hsinh : x / 2 ≤ Real.sinh (x / 2) := by
        exact Real.self_le_sinh_iff.mpr (by linarith)
      have hden : x ≤ 2 * Real.sinh (x / 2) := by linarith
      have hdenpos : 0 < 2 * Real.sinh (x / 2) := by
        positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenpos]
      apply (div_le_iff₀ hdenpos).2
      calc
        |1 - F x| = (|1 - F x| / x) * x := by
          field_simp
        _ ≤ (|1 - F x| / x) * (2 * Real.sinh (x / 2)) := by
          exact mul_le_mul_of_nonneg_left hden (by positivity)
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  let S : ℝ := max R 1 + 2
  have hS1 : 1 ≤ S := by
    dsimp [S]
    linarith [le_max_right R 1]
  have hFzero : ∀ x ∈ Ioi S, F x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport F := by
      intro hxt
      have hxball : x ∈ Metric.closedBall (0 : ℝ) R := hR hxt
      have hxdist : dist x 0 ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
      have hxle : x ≤ R := by
        have hxpos : 0 < x := lt_trans (by linarith [hS1]) hx
        simpa only [Real.dist_eq, sub_zero, abs_of_pos hxpos] using hxdist
      have hSR : R < S := by
        dsimp [S]
        linarith [le_max_left R 1]
      exact (not_lt_of_ge hxle) (lt_trans hSR hx)
    exact image_eq_zero_of_notMem_tsupport hxnot
  have hCbasecont : Continuous (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) := by
    have hhalf : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const _
    have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) :=
      continuous_const.mul (Real.continuous_cosh.comp hhalf)
    apply Continuous.div continuous_const hden
    intro x
    positivity
  have hCoshBound : ∀ x ∈ Ioi 0, Real.exp (x / 2) ≤ 2 * Real.cosh (x / 2) := by
    intro x hx
    rw [Real.cosh_eq]
    have hexp : 0 ≤ Real.exp (-(x / 2)) := Real.exp_nonneg _
    nlinarith
  have hExpTail : IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Ioi S) := by
    convert (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) S) using 1
    ext x
    congr 1
    ring
  have hCbaseTail : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioi S) := by
    show Integrable (fun x : ℝ => 1 / (2 * Real.cosh (x / 2)))
      (volume.restrict (Ioi S))
    apply hExpTail.integrable.mono'
    · exact hCbasecont.measurable.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := lt_trans (by linarith [hS1]) hx
      have hdenpos : 0 < 2 * Real.cosh (x / 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      apply (div_le_iff₀ hdenpos).2
      have hprod : 1 ≤ Real.exp (-x / 2) * (2 * Real.cosh (x / 2)) := by
        calc
          1 = Real.exp (-x / 2) * Real.exp (x / 2) := by
            rw [← Real.exp_add]
            ring_nf
            simp
          _ ≤ Real.exp (-x / 2) * (2 * Real.cosh (x / 2)) :=
            mul_le_mul_of_nonneg_left (hCoshBound x hxpos) (by positivity)
      exact hprod
  have hCbaseSmall : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioc 0 S) := by
    exact (hCbasecont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hCbase : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioi 0) := by
    have hu := hCbaseSmall.union hCbaseTail
    have hsub : Ioi 0 ⊆ Ioc 0 S ∪ Ioi S := by
      intro x hx
      by_cases hxs : x ≤ S
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr (lt_of_not_ge hxs)
    exact hu.mono_set hsub
  have hCdivcont : Continuous
      (fun x : ℝ => F x / (2 * Real.cosh (x / 2))) := by
    have hhalf : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const _
    have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) :=
      continuous_const.mul (Real.continuous_cosh.comp hhalf)
    apply Continuous.div hcont hden
    intro x
    positivity
  have hCdivcompact : HasCompactSupport
      (fun x : ℝ => F x / (2 * Real.cosh (x / 2))) := by
    have hEq : (fun x : ℝ => F x / (2 * Real.cosh (x / 2))) =
        F * (fun x : ℝ => (2 * Real.cosh (x / 2))⁻¹) := by
      funext x
      simp only [Pi.mul_apply, div_eq_mul_inv]
    rw [hEq]
    exact hcompact.mul_right
  have hCdiv : IntegrableOn
      (fun x : ℝ => F x / (2 * Real.cosh (x / 2))) (Ioi 0) :=
    (hCdivcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hCdivcompact).integrableOn
  have hC : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2))) (Ioi 0) := by
    have hsub := hCbase.sub hCdiv
    convert hsub using 1
    ext x
    have hden : 2 * Real.cosh (x / 2) ≠ 0 := by positivity
    simp only [Pi.sub_apply]
    field_simp [hden]
  let c : ℝ := 1 - Real.exp (-1)
  have hcpos : 0 < c := by
    dsimp [c]
    have he : Real.exp (-1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  have hSinhBound : ∀ x ∈ Ioi S,
      c * Real.exp (x / 2) ≤ 2 * Real.sinh (x / 2) := by
    intro x hx
    change S < x at hx
    have hexp : Real.exp (-x) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      linarith [hS1, hx]
    have hdiff : c ≤ 1 - Real.exp (-x) := by
      dsimp [c]
      linarith
    have hident : 2 * Real.sinh (x / 2) =
        Real.exp (x / 2) * (1 - Real.exp (-x)) := by
      rw [Real.sinh_eq]
      field_simp
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 1
      ring_nf
    rw [hident]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg (x / 2))
  have hBmidcont : ContinuousOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Icc 1 S) := by
    have hhalf : Continuous (fun x : ℝ => x / 2) := continuous_id.div_const _
    have hnum : ContinuousOn (fun x : ℝ => 1 - F x) (Icc 1 S) :=
      (continuous_const.sub hcont).continuousOn
    have hden : ContinuousOn (fun x : ℝ => 2 * Real.sinh (x / 2)) (Icc 1 S) :=
      (continuous_const.mul (Real.continuous_sinh.comp hhalf)).continuousOn
    exact hnum.div hden (by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
      positivity)
  have hBmid : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Icc 1 S) := by
    exact hBmidcont.integrableOn_compact isCompact_Icc
  have hBtail : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi S) := by
    have hmajor : IntegrableOn
        (fun x : ℝ => c⁻¹ * Real.exp (-x / 2)) (Ioi S) := by
      show Integrable (fun x : ℝ => c⁻¹ * Real.exp (-x / 2))
        (volume.restrict (Ioi S))
      simpa only [mul_comm] using hExpTail.integrable.const_mul c⁻¹
    show Integrable (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2)))
      (volume.restrict (Ioi S))
    apply hmajor.integrable.mono'
    · exact ((measurable_const.sub hcont.measurable).div
        (measurable_const.mul
          (Real.continuous_sinh.measurable.comp
            (measurable_id.div measurable_const)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := lt_trans (by linarith [hS1]) hx
      have hdenpos : 0 < 2 * Real.sinh (x / 2) := by positivity
      rw [hFzero x hx, sub_zero, Real.norm_eq_abs, abs_div,
        abs_of_pos hdenpos, abs_one]
      apply (div_le_iff₀ hdenpos).2
      have hmul := mul_le_mul_of_nonneg_left (hSinhBound x hx)
        (by positivity : 0 ≤ c⁻¹ * Real.exp (-x / 2))
      calc
        1 = (c⁻¹ * Real.exp (-x / 2)) * (c * Real.exp (x / 2)) := by
          field_simp [ne_of_gt hcpos]
          rw [← Real.exp_add]
          ring_nf
          simp
        _ ≤ (c⁻¹ * Real.exp (-x / 2)) * (2 * Real.sinh (x / 2)) := hmul
  have hBrest : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 1) := by
    have hu := hBmid.union hBtail
    apply hu.mono_set
    intro x hx
    by_cases hxs : x ≤ S
    · exact Or.inl ⟨le_of_lt hx, hxs⟩
    · exact Or.inr (lt_of_not_ge hxs)
  have hB : IntegrableOn
      (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) (by norm_num)]
    exact hBsmall.union hBrest
  exact ⟨hA, hB, hC⟩

theorem chapter08_root_discriminant_log_eq_div
    (hK : 0 < Chapter08Degree K) :
    Real.log (Chapter08RootDiscriminant K) =
      Real.log (Chapter08AbsoluteDiscriminant K) / (Chapter08Degree K : ℝ) := by
  change Real.log (NumberField.rootDiscr K) =
    Real.log (|(NumberField.discr K : ℝ)|) / (Module.finrank ℚ K : ℝ)
  have hd : 0 < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr hK
  rw [NumberField.rootDiscr_def, Real.log_rpow]
  · simp only [Int.cast_abs]
    field_simp [ne_of_gt hd]
  · exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero K))

/-!
Dropping the nonnegative zero and prime contributions in the earlier explicit formula gives the
book's equation (8.2).
-/
theorem chapter08_root_discriminant_lower_bound
    {F : ℝ → ℝ} (hK : 0 < Chapter08Degree K)
    (hformula : Chapter08ExplicitFormulaData K F)
    (hzero : 0 ≤ hformula.zeroContribution)
    (hprime : 0 ≤ hformula.primeContribution) :
    Real.log (Chapter08RootDiscriminant K) ≥
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        chapter08SignatureProportion K * (Real.pi / 2) -
        4 * chapter08A F / (Chapter08Degree K : ℝ) -
        chapter08B F -
        chapter08SignatureProportion K * chapter08C F := by
  have hd : 0 < (Chapter08Degree K : ℝ) := Nat.cast_pos.mpr hK
  rw [chapter08_root_discriminant_log_eq_div hK, chapter08SignatureProportion]
  apply (le_div_iff₀ hd).2
  rw [hformula.identity]
  field_simp
  nlinarith

theorem chapter08_pole_cost_tends_to_zero (F : ℝ → ℝ) :
    Tendsto (fun n : ℕ => 4 * chapter08A F / (n : ℝ)) atTop (𝓝 0) := by
  exact Filter.Tendsto.const_div_atTop tendsto_natCast_atTop_atTop (4 * chapter08A F)

theorem chapter08_signature_correction_nonnegative
    {F : ℝ → ℝ}
    (hα : 0 ≤ chapter08SignatureProportion K)
    (hC : chapter08C F ≤ Real.pi / 2) :
    0 ≤ chapter08SignatureProportion K * (Real.pi / 2 - chapter08C F) := by
  exact mul_nonneg hα (sub_nonneg.mpr hC)

theorem chapter08_signature_correction_strictly_favorable
    (hα : 0 < chapter08SignatureProportion K) {F : ℝ → ℝ}
    (hC : chapter08C F < Real.pi / 2) :
    0 < chapter08SignatureProportion K * (Real.pi / 2 - chapter08C F) := by
  exact mul_pos hα (sub_pos.mpr hC)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
