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

private theorem chapter08_bounded_variation_on_univ_of_compact_support
    {f : ℝ → ℝ} (hcompact : HasCompactSupport f)
    (hlocal : ∀ a b : ℝ, BoundedVariationOn f (Set.uIcc a b)) :
    BoundedVariationOn f Set.univ := by
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  let S : ℝ := max R 0 + 1
  have hS : 0 ≤ S := by
    dsimp [S]
    linarith [le_max_right R 0]
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [le_max_right R 0]
  have hRltS : R < S := by
    dsimp [S]
    linarith [le_max_left R 0]
  have hzero : ∀ x : ℝ, x ≤ -S ∨ S ≤ x → f x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport f := by
      intro hxt
      have hxball : x ∈ Metric.closedBall (0 : ℝ) R := hR hxt
      have hxdist : dist x 0 ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
      have habs : |x| ≤ R := by
        simpa only [Real.dist_eq, sub_zero] using hxdist
      rcases hx with hxleft | hxright
      · have hxneg : x < 0 := lt_of_le_of_lt hxleft (by linarith [hSpos])
        have hSabs : S ≤ |x| := by
          rw [abs_of_neg hxneg]
          linarith
        exact (not_lt_of_ge habs) (lt_of_lt_of_le hRltS hSabs)
      · have hxpos : 0 < x := lt_of_lt_of_le hSpos hxright
        have hSabs : S ≤ |x| := by
          rw [abs_of_pos hxpos]
          exact hxright
        exact (not_lt_of_ge habs) (lt_of_lt_of_le hRltS hSabs)
    exact image_eq_zero_of_notMem_tsupport hxnot
  have hboundary : f (-S) = 0 ∧ f S = 0 := by
    exact ⟨hzero (-S) (Or.inl le_rfl), hzero S (Or.inr le_rfl)⟩
  have hclamp_mem : ∀ x : ℝ,
      max (-S) (min x S) ∈ Set.Icc (-S) S := by
    intro x
    constructor
    · exact le_max_left _ _
    · apply max_le
      · linarith
      · exact min_le_right _ _
  have hclamp_eq : ∀ x : ℝ,
      f x = f (max (-S) (min x S)) := by
    intro x
    by_cases hxleft : x < -S
    · have hfx : f x = 0 := hzero x (Or.inl hxleft.le)
      have hclamp : max (-S) (min x S) = -S := by
        rw [min_eq_left (by linarith [hxleft, hS]), max_eq_left hxleft.le]
      rw [hfx, hclamp, hboundary.1]
    · by_cases hxright : S < x
      · have hfx : f x = 0 := hzero x (Or.inr hxright.le)
        have hclamp : max (-S) (min x S) = S := by
          rw [min_eq_right hxright.le, max_eq_right (by linarith [hS])]
        rw [hfx, hclamp, hboundary.2]
      · have hxleft' : -S ≤ x := le_of_not_gt hxleft
        have hxright' : x ≤ S := le_of_not_gt hxright
        simp [max_eq_right hxleft', min_eq_left hxright']
  have hle : eVariationOn f Set.univ ≤ eVariationOn f (Set.Icc (-S) S) := by
    rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, hu_mem⟩
    let v : ℕ → ℝ := fun i => max (-S) (min (u i) S)
    have hv : Monotone v := by
      intro i j hij
      dsimp [v]
      exact max_le_max le_rfl (min_le_min (hu hij) le_rfl)
    have hv_mem : ∀ i, v i ∈ Set.Icc (-S) S := by
      intro i
      exact hclamp_mem (u i)
    calc
      (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n,
            edist (f (v (i + 1))) (f (v i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        change edist (f (u (i + 1))) (f (u i)) =
          edist (f (max (-S) (min (u (i + 1)) S)))
            (f (max (-S) (min (u i) S)))
        exact congrArg₂ edist (hclamp_eq (u (i + 1))) (hclamp_eq (u i))
      _ ≤ eVariationOn f (Set.Icc (-S) S) :=
        eVariationOn.sum_le hv hv_mem
  have hcentral : BoundedVariationOn f (Set.Icc (-S) S) := by
    have h := hlocal (-S) S
    rw [Set.uIcc_of_le (by linarith [hS])] at h
    exact h
  exact ne_top_of_le_ne_top hcentral hle

private theorem chapter08_derivative_eq_zero_of_eventually_zero
    {F D : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hderiv : HasDerivWithinAt F (D x) s x)
    (hevent : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[s] x] F)
    (hvalue : F x = 0) (hunique : UniqueDiffWithinAt ℝ s x) :
    D x = 0 := by
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (D x) s x :=
    hderiv.congr_of_eventuallyEq hevent hvalue.symm
  have hzero : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 s x :=
    hasDerivWithinAt_const (x := x) (s := s) (c := (0 : ℝ))
  exact (hconst.derivWithin hunique).symm.trans
    (hzero.derivWithin hunique)

private theorem chapter08_one_sided_derivatives_have_compact_support
    {F Dleft Dright : ℝ → ℝ} (hcompact : HasCompactSupport F)
    (hleft : ∀ x, HasDerivWithinAt F (Dleft x) (Set.Iic x) x)
    (hright : ∀ x, HasDerivWithinAt F (Dright x) (Set.Ici x) x) :
    HasCompactSupport Dleft ∧ HasCompactSupport Dright := by
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  let S : ℝ := max R 0 + 1
  have hS : 0 ≤ S := by
    dsimp [S]
    linarith [le_max_right R 0]
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [le_max_right R 0]
  have hRltS : R < S := by
    dsimp [S]
    linarith [le_max_left R 0]
  have hzeroF : ∀ x : ℝ, x ≤ -S ∨ S ≤ x → F x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport F := by
      intro hxt
      have hxball : x ∈ Metric.closedBall (0 : ℝ) R := hR hxt
      have hxdist : dist x 0 ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
      have habs : |x| ≤ R := by
        simpa only [Real.dist_eq, sub_zero] using hxdist
      rcases hx with hxleft | hxright
      · have hxneg : x < 0 := lt_of_le_of_lt hxleft (by linarith [hSpos])
        have hSabs : S ≤ |x| := by
          rw [abs_of_neg hxneg]
          linarith
        exact (not_lt_of_ge habs) (lt_of_lt_of_le hRltS hSabs)
      · have hxpos : 0 < x := lt_of_lt_of_le hSpos hxright
        have hSabs : S ≤ |x| := by
          rw [abs_of_pos hxpos]
          exact hxright
        exact (not_lt_of_ge habs) (lt_of_lt_of_le hRltS hSabs)
    exact image_eq_zero_of_notMem_tsupport hxnot
  have hDleft_zero : ∀ x, x ∉ Set.Icc (-S) S → Dleft x = 0 := by
    intro x hx
    have hx' : x < -S ∨ S < x := by
      by_cases hleft : x < -S
      · exact Or.inl hleft
      · right
        exact lt_of_not_ge (fun hright => hx ⟨le_of_not_gt hleft, hright⟩)
    rcases hx' with hxleft | hxright
    · have hevent : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Set.Iic x] x] F := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hzeroF y (Or.inl (le_trans hy hxleft.le))).symm
      exact chapter08_derivative_eq_zero_of_eventually_zero (hleft x) hevent
        (hzeroF x (Or.inl hxleft.le)) (uniqueDiffWithinAt_Iic x)
    · have hevent : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Set.Iic x] x] F := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hxright)] with y hy
        exact (hzeroF y (Or.inr hy.le)).symm
      exact chapter08_derivative_eq_zero_of_eventually_zero (hleft x) hevent
        (hzeroF x (Or.inr hxright.le)) (uniqueDiffWithinAt_Iic x)
  have hDright_zero : ∀ x, x ∉ Set.Icc (-S) S → Dright x = 0 := by
    intro x hx
    have hx' : x < -S ∨ S < x := by
      by_cases hleft : x < -S
      · exact Or.inl hleft
      · right
        exact lt_of_not_ge (fun hright => hx ⟨le_of_not_gt hleft, hright⟩)
    rcases hx' with hxleft | hxright
    · have hevent : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Set.Ici x] x] F := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxleft)] with y hy
        exact (hzeroF y (Or.inl hy.le)).symm
      exact chapter08_derivative_eq_zero_of_eventually_zero (hright x) hevent
        (hzeroF x (Or.inl hxleft.le)) (uniqueDiffWithinAt_Ici x)
    · have hevent : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Set.Ici x] x] F := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hzeroF y (Or.inr (le_trans hxright.le hy))).symm
      exact chapter08_derivative_eq_zero_of_eventually_zero (hright x) hevent
        (hzeroF x (Or.inr hxright.le)) (uniqueDiffWithinAt_Ici x)
  refine ⟨?_, ?_⟩
  · apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    exact hDleft_zero x hx
  · apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    exact hDright_zero x hx

/-!
The Chapter 6 explicit formula uses the canonical Chapter 5 admissibility class.  This bridge
keeps the Chapter 8-facing piecewise formulation available while exposing the canonical class
required by the zero and prime summability interfaces.
-/
theorem chapter08_basically_admissible_to_chapter06
    {F : ℝ → ℝ} (hF : Chapter08BasicallyAdmissible F) :
    Chapter06.Chapter06BasicallyAdmissible F := by
  rcases hF with ⟨heven, hcont, hcompact, hpiece, hderiv, hF0, hnear⟩
  refine
    { even := heven
      continuous := hcont
      compactSupport := hcompact
      piecewiseC2 := ?_
      valueAtZero := hF0
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · rcases hpiece with ⟨s, hs⟩
    refine ⟨(s : Set ℝ), s.finite_toSet, ?_⟩
    intro x hx
    rcases hs x hx with ⟨ε, hε, hdiff⟩
    apply hdiff.contDiffAt
    exact isOpen_Ioo.mem_nhds (by constructor <;> linarith)
  · rcases hderiv with ⟨Dleft, Dright, hleftBV, hrightBV, hderiv⟩
    have hcompactD := chapter08_one_sided_derivatives_have_compact_support hcompact
      (fun x => (hderiv x).2) (fun x => (hderiv x).1)
    refine ⟨Dleft, Dright, ?_, ?_, ?_, ?_⟩
    · intro x
      exact (hderiv x).2
    · intro x
      exact (hderiv x).1
    · exact chapter08_bounded_variation_on_univ_of_compact_support
        hcompactD.1 hleftBV
    · exact chapter08_bounded_variation_on_univ_of_compact_support
        hcompactD.2 hrightBV
  · exact (Chapter05.chapter05_origin_condition_iff_integrableOn hcont).2 hnear

theorem chapter08_unconditionally_admissible_to_chapter06
    {F : ℝ → ℝ} (hF : Chapter08UnconditionallyAdmissible F) :
    Chapter06.Chapter06UnconditionallyAdmissible F := by
  rcases hF with ⟨hbasic, G, heven, hnonnegative, hpositive, hshape⟩
  refine ⟨chapter08_basically_admissible_to_chapter06 hbasic, ?_⟩
  exact ⟨G, hnonnegative, heven, hpositive, hshape⟩

theorem chapter08_grh_admissible_to_chapter06
    {F : ℝ → ℝ} (hF : Chapter08GRHAdmissible F) :
    Chapter06.Chapter06GRHAdmissible F := by
  refine
    { basic := chapter08_basically_admissible_to_chapter06 hF.1
      pointwiseNonnegative := hF.2.1
      transformNonnegative := hF.2.2.transformNonnegative }

theorem chapter08_canonical_zero_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08BasicallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      Chapter06.chapter06ZeroSummand (chapter08CanonicalZeroSpectrum K) F ρ) := by
  simpa [chapter08CanonicalZeroSpectrum] using
    (Chapter06.chapter06_canonical_zero_summand_summable K
      (chapter08_basically_admissible_to_chapter06 hF))

theorem chapter08_canonical_prime_power_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08BasicallyAdmissible F) :
    Summable (fun q : Chapter06.Chapter06PrimePower K =>
      Chapter06.chapter06PrimePowerTerm F q) := by
  apply summable_of_hasFiniteSupport
  exact Chapter06.chapter06_prime_power_support_finite K
    (chapter08_basically_admissible_to_chapter06 hF)

theorem chapter08_canonical_prime_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08BasicallyAdmissible F) (hFnonnegative : ∀ x, 0 ≤ F x) :
    0 ≤ chapter08CanonicalPrimeContribution K F := by
  simpa [chapter08CanonicalPrimeContribution] using
    (Chapter06.chapter06_prime_contribution_nonnegative K
      (chapter08_basically_admissible_to_chapter06 hF) hFnonnegative)

theorem chapter08_canonical_unconditional_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08UnconditionallyAdmissible F) :
    0 ≤ chapter08CanonicalZeroContribution K F := by
  simpa [chapter08CanonicalZeroContribution, chapter08CanonicalZeroSpectrum] using
    (Chapter06.chapter06_canonical_unconditional_zero_contribution_nonnegative K
      (chapter08_unconditionally_admissible_to_chapter06 hF))

theorem chapter08_canonical_grh_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08GRHAdmissible F)
    (hGRH : Chapter06.chapter06GRH (chapter08CanonicalZeroSpectrum K)) :
    0 ≤ chapter08CanonicalZeroContribution K F := by
  simpa [chapter08CanonicalZeroContribution, chapter08CanonicalZeroSpectrum] using
    (Chapter06.chapter06_canonical_grh_zero_contribution_nonnegative K
      (chapter08_grh_admissible_to_chapter06 hF) hGRH)

/-!
The canonical bridge used by both triangular regimes.  Its zero and prime fields are the terms
from the canonical Chapter 6 zeta package, while the Chapter 8 admissibility field remains the
one consumed by `chapter08_root_discriminant_lower_bound`.
-/
noncomputable def chapter08CanonicalExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08BasicallyAdmissible F) :
    Chapter08ExplicitFormulaData K F where
  basicAdmissible := hF
  zeroContribution := chapter08CanonicalZeroContribution K F
  primeContribution := chapter08CanonicalPrimeContribution K F
  identity := by
    simpa [Chapter08AbsoluteDiscriminant, Chapter08Degree, Chapter08RealPlaceCount,
      chapter08A, chapter08B, chapter08C, chapter08CanonicalZeroContribution,
      chapter08CanonicalZeroSpectrum, chapter08CanonicalPrimeContribution,
      Chapter06.chapter06AbsoluteDiscriminant, Chapter06.chapter06Degree,
      Chapter06.chapter06RealPlaces, Chapter06.chapter06A, Chapter06.chapter06B,
      Chapter06.chapter06C] using
      (Chapter06.chapter06_weil_poitou_explicit_formula_expanded K
        (Chapter06.chapter06CanonicalZetaAnalyticPackage K)
        (chapter08_basically_admissible_to_chapter06 hF))

noncomputable def chapter08CanonicalUnconditionalExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08UnconditionallyAdmissible F) :
    Chapter08ExplicitFormulaData K F :=
  chapter08CanonicalExplicitFormulaData K hF.1

noncomputable def chapter08CanonicalGRHExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter08GRHAdmissible F) :
    Chapter08ExplicitFormulaData K F :=
  chapter08CanonicalExplicitFormulaData K hF.1

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
