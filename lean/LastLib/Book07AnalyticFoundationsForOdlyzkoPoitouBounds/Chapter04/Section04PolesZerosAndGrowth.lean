import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section03ContinuationAndFunctionalEquation
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section02EulerProducts
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

open Filter MeasureTheory NumberField Set Topology
open scoped BigOperators ComplexConjugate nonZeroDivisors

/-! ### 4.4. Poles, zeros, and growth -/

/-- The pole-removing factor in the definition of `ξ_K`. -/
noncomputable def chapter04PoleFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)

/-- The completed entire function attached to the Dedekind zeta function. -/
noncomputable def chapter04Xi
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  if s = 0 ∨ s = 1 then
    (Fintype.card (ClassGroup (𝓞 K)) : ℂ) /
      ((2 : ℂ) * (chapter04MellinConstant K
        (chapter04ChosenUnitFundamentalDomain K) : ℂ))
  else
      chapter04PoleFactor s * chapter04CompletedDedekindZeta K s

theorem chapter04_completed_dedekind_zeta_trailing_coeff_at_one
    (K : Type*) [Field K] [NumberField K] :
    meromorphicTrailingCoeffAt (chapter04CompletedDedekindZeta K) 1 =
      (Fintype.card (ClassGroup (𝓞 K)) : ℂ) *
        (chapter04MellinConstant K
          (chapter04ChosenUnitFundamentalDomain K) : ℂ)⁻¹ := by
  classical
  let D := chapter04ChosenUnitFundamentalDomain K
  let scale : ℂ := (chapter04MellinConstant K D : ℂ)⁻¹
  let q : ℂ → ℂ := chapter04ZeroVectorCorrection
  let p : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04ThetaMellinTail K D
        (chapter04FractionalIdealRepresentative K C⁻¹) z +
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K
          (chapter04FractionalIdealRepresentative K C⁻¹ :
            Chapter04FractionalIdeal K)) (1 - z)
  let f : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04CompletedPartialZetaContinuation K D C z
  let P : ℂ → ℂ := fun z =>
    ∑ C : ClassGroup (𝓞 K), scale * p C z
  let c : ℂ := (Fintype.card (ClassGroup (𝓞 K)) : ℂ) * scale
  have hscale : scale ≠ 0 := by
    simp [scale, chapter04_mellin_constant_ne_zero K D]
  have hdecomp (C : ClassGroup (𝓞 K)) :
      f C = fun z => scale * (p C z + q z) := by
    funext z
    simp [f, p, q, scale, D, chapter04CompletedPartialZetaContinuation,
      chapter04CompletedPartialZetaForIdeal]
  have hp (C : ClassGroup (𝓞 K)) (z : ℂ) :
      AnalyticAt ℂ (p C) z := by
    apply (chapter04_theta_mellin_tail_entire K D
      (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)) z
      (Set.mem_univ _)).add
    simpa [p, Function.comp_def] using
      ((chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K
          (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)))
        (1 - z) (Set.mem_univ _)).comp (by fun_prop))
  have hP (z : ℂ) : AnalyticAt ℂ P z := by
    have hsum : AnalyticAt ℂ
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) z := by
      apply Finset.analyticAt_sum Finset.univ
      intro C hC
      exact analyticAt_const.mul (hp C z)
    have hfun :
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) = P := by
      funext w
      rw [Finset.sum_apply]
    rw [← hfun]
    exact hsum
  have hq_order : meromorphicOrderAt q 1 = (-1 : ℤ) := by
    unfold q chapter04ZeroVectorCorrection
    change meromorphicOrderAt
      ((fun z : ℂ => (1 : ℂ) / (z - 1)) +
        (fun z : ℂ => -(1 / z))) 1 = (-1 : ℤ)
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 1 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 1)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun z : ℂ => z) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun z : ℂ => 1 / z) (x := 1)).symm.trans h₂
      change meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 at hneg
      exact hneg
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_left
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  have hq_mer : MeromorphicAt q 1 := by
    change MeromorphicAt (fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z) 1
    fun_prop
  have hq_res : meromorphicTrailingCoeffAt q 1 = (1 : ℂ) := by
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 1 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 1)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun z : ℂ => z) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have hleft :
        meromorphicTrailingCoeffAt
            (fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z) 1 =
          meromorphicTrailingCoeffAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 := by
      exact MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
        (f₁ := fun z : ℂ => (1 : ℂ) / (z - 1))
        (f₂ := fun z : ℂ => (1 : ℂ) / z) (by fun_prop) (by
          rw [h₁, h₂]
          exact WithTop.coe_lt_coe.mpr (by norm_num))
    rw [show q = fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z by
      funext z
      rfl, hleft]
    have hlin : meromorphicTrailingCoeffAt (fun z : ℂ => z - 1) 1 = (1 : ℂ) := by
      simpa using
        (meromorphicTrailingCoeffAt_id_sub_const (x := (1 : ℂ)) (y := (1 : ℂ)))
    have hinv : meromorphicTrailingCoeffAt (fun z : ℂ => (z - 1)⁻¹) 1 = (1 : ℂ) := by
      rw [meromorphicTrailingCoeffAt_fun_inv, hlin]
      norm_num
    simpa only [one_div] using hinv
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ClassGroup (𝓞 K)) ≠ 0)
    · exact hscale
  have hsecond_mer : MeromorphicAt (fun z : ℂ => c * q z) 1 := by
    change MeromorphicAt
      (fun z : ℂ => c * ((1 : ℂ) / (z - 1) - 1 / z)) 1
    fun_prop
  have hsecond_order :
      meromorphicOrderAt (fun z : ℂ => c * q z) 1 = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun _ : ℂ => c) * q) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_mul_of_ne_zero (by fun_prop) hc, hq_order]
  have hdecomp_sum (z : ℂ) :
      chapter04CompletedDedekindZeta K z = P z + c * q z := by
    unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
    rw [tsum_fintype]
    change (∑ C : ClassGroup (𝓞 K), f C z) = _
    simp_rw [hdecomp]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    change (∑ C : ClassGroup (𝓞 K), scale * p C z) +
        (∑ C : ClassGroup (𝓞 K), scale * q z) = P z + c * q z
    rw [show (∑ C : ClassGroup (𝓞 K), scale * p C z) = P z by rfl]
    congr 1
    rw [← Finset.sum_mul]
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [c, mul_assoc]
  have hdecomp_fun :
      chapter04CompletedDedekindZeta K = (fun z => P z + c * q z) := by
    funext z
    exact hdecomp_sum z
  have hres_total :
      meromorphicTrailingCoeffAt (chapter04CompletedDedekindZeta K) 1 =
        meromorphicTrailingCoeffAt (fun z : ℂ => c * q z) 1 := by
    rw [hdecomp_fun]
    change meromorphicTrailingCoeffAt
      ((fun z : ℂ => P z) + (fun z : ℂ => c * q z)) 1 = _
    have hcomm :
        (fun z : ℂ => P z) + (fun z : ℂ => c * q z) =
          (fun z : ℂ => c * q z) + (fun z : ℂ => P z) := by
      funext z
      simp [add_comm]
    rw [hcomm]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt
      (hP 1).meromorphicAt
    rw [hsecond_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num))
      (hP 1).meromorphicOrderAt_nonneg
  have hres_scaled :
      meromorphicTrailingCoeffAt (fun z : ℂ => c * q z) 1 =
        c * meromorphicTrailingCoeffAt q 1 := by
    simpa only [Pi.mul_apply, meromorphicTrailingCoeffAt_const] using
      (MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
        (f₁ := fun _ : ℂ => c) (f₂ := q) (by fun_prop) hq_mer)
  rw [hres_total, hres_scaled, hq_res]
  simp [c, scale, D]

theorem chapter04_xi_eq_pole_factor_mul_completed_zeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    chapter04Xi K s =
      (1 / 2 : ℂ) * s * (s - 1) * chapter04CompletedDedekindZeta K s := by
  simp [chapter04Xi, hs0, hs1, chapter04PoleFactor]

theorem chapter04_xi_entire
    (K : Type*) [Field K] [NumberField K] :
    AnalyticOnNhd ℂ (chapter04Xi K) Set.univ := by
  intro s hs
  classical
  by_cases hs0 : s = 0
  · subst s
    let f : ℂ → ℂ := chapter04PoleFactor * chapter04CompletedDedekindZeta K
    have hpole_an0 : AnalyticAt ℂ chapter04PoleFactor (0 : ℂ) := by
      unfold chapter04PoleFactor
      fun_prop
    have hpole_mer0 : MeromorphicAt chapter04PoleFactor (0 : ℂ) :=
      hpole_an0.meromorphicAt
    have hzeta_mer0 : MeromorphicAt (chapter04CompletedDedekindZeta K) (0 : ℂ) :=
      chapter04_completed_dedekind_zeta_meromorphic K 0
    have hf0 : MeromorphicAt f 0 := by
      exact hpole_mer0.mul hzeta_mer0
    have hpole_order0 : meromorphicOrderAt chapter04PoleFactor 0 = (1 : ℤ) := by
      apply (meromorphicOrderAt_eq_int_iff hpole_mer0).2
      refine ⟨fun z : ℂ => (1 / 2 : ℂ) * (z - 1),
        analyticAt_const.mul (analyticAt_id.sub analyticAt_const), by norm_num, ?_⟩
      filter_upwards [] with z
      simp [chapter04PoleFactor]
      ring_nf
    have horder0 : meromorphicOrderAt f 0 = 0 := by
      have hmul := meromorphicOrderAt_mul hpole_mer0 hzeta_mer0
      calc
        meromorphicOrderAt f 0 =
            meromorphicOrderAt chapter04PoleFactor 0 +
              meromorphicOrderAt (chapter04CompletedDedekindZeta K) 0 := by
          simpa [f] using hmul
        _ = 0 := by
          rw [hpole_order0,
            (chapter04_completed_dedekind_zeta_simple_poles K).1]
          norm_num
    have hpole_an1 : AnalyticAt ℂ chapter04PoleFactor (1 : ℂ) := by
      unfold chapter04PoleFactor
      fun_prop
    have hpole_mer1 : MeromorphicAt chapter04PoleFactor (1 : ℂ) :=
      hpole_an1.meromorphicAt
    have hzeta_mer1 : MeromorphicAt (chapter04CompletedDedekindZeta K) (1 : ℂ) :=
      chapter04_completed_dedekind_zeta_meromorphic K 1
    have horder1 : meromorphicOrderAt f 1 = 0 := by
      have hmul := meromorphicOrderAt_mul hpole_mer1 hzeta_mer1
      have hpole_order1 : meromorphicOrderAt chapter04PoleFactor 1 = (1 : ℤ) := by
        apply (meromorphicOrderAt_eq_int_iff hpole_mer1).2
        refine ⟨fun z : ℂ => (1 / 2 : ℂ) * z,
          analyticAt_const.mul analyticAt_id, by norm_num, ?_⟩
        filter_upwards [] with z
        simp [chapter04PoleFactor]
        ring_nf
      calc
        meromorphicOrderAt f 1 =
            meromorphicOrderAt chapter04PoleFactor 1 +
              meromorphicOrderAt (chapter04CompletedDedekindZeta K) 1 := by
          simpa [f] using hmul
        _ = 0 := by
          rw [hpole_order1,
            (chapter04_completed_dedekind_zeta_simple_poles K).2.1]
          norm_num
    have hpole_res1 : meromorphicTrailingCoeffAt chapter04PoleFactor 1 = (1 / 2 : ℂ) := by
      have hres' :=
        (analyticAt_const.mul analyticAt_id).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
          (f := chapter04PoleFactor) (x := (1 : ℂ))
          (g := fun z : ℂ => (1 / 2 : ℂ) * z) (n := 1) (by norm_num) (by
            filter_upwards [] with z
            simp [chapter04PoleFactor]
            ring_nf)
      simpa using hres'
    have hres1 : meromorphicTrailingCoeffAt f 1 =
        (Fintype.card (ClassGroup (𝓞 K)) : ℂ) /
          ((2 : ℂ) * (chapter04MellinConstant K
            (chapter04ChosenUnitFundamentalDomain K) : ℂ)) := by
      change meromorphicTrailingCoeffAt
        (fun z : ℂ => chapter04PoleFactor z * chapter04CompletedDedekindZeta K z) 1 = _
      have hprod := MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul hpole_mer1 hzeta_mer1
      rw [hprod, hpole_res1,
        chapter04_completed_dedekind_zeta_trailing_coeff_at_one K]
      field_simp [chapter04_mellin_constant_ne_zero K
        (chapter04ChosenUnitFundamentalDomain K)]
    let g : ℂ → ℂ := fun z => 1 - z
    have hg : AnalyticAt ℂ g (0 : ℂ) := by
      unfold g
      fun_prop
    have hg_nc : ¬EventuallyConst g (𝓝 (0 : ℂ)) := by
      simp only [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
      have hneg : analyticOrderAt (fun z : ℂ => -z) 0 = (1 : ℕ∞) := by
        apply (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0).analyticOrderAt_eq_natCast.mpr
        refine ⟨fun _ => (-1 : ℂ), by fun_prop, by norm_num, ?_⟩
        filter_upwards [] with z
        simp
      rw [show (g · - g 0) = (fun z : ℂ => -z) by
        funext z
        simp [g], hneg]
      exact ENat.one_ne_top
    have hcomp : f ∘ g = f := by
      funext z
      dsimp [f, g]
      have hpole : chapter04PoleFactor (1 - z) = chapter04PoleFactor z := by
        unfold chapter04PoleFactor
        ring
      rw [hpole, chapter04_completed_dedekind_zeta_functional_equation K z]
    have hcomp_coeff :=
      MeromorphicAt.meromorphicTrailingCoeffAt_comp
        (f := f) (x := (0 : ℂ)) (g := g)
        (by simpa [f, g] using hpole_mer1.mul hzeta_mer1) hg hg_nc
    have hres0 : meromorphicTrailingCoeffAt f 0 =
        meromorphicTrailingCoeffAt f 1 := by
      calc
        meromorphicTrailingCoeffAt f 0 = meromorphicTrailingCoeffAt (f ∘ g) 0 := by
          rw [hcomp]
        _ = meromorphicTrailingCoeffAt f 1 := by
          rw [hcomp_coeff]
          simp [g, horder1]
    have hvalue : chapter04Xi K 0 = meromorphicTrailingCoeffAt f 0 := by
      simp [chapter04Xi]
      rw [hres0, hres1]
    have hlim : Tendsto f (𝓝[≠] (0 : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt f 0)) := by
      simpa [horder0] using hf0.tendsto_nhds_meromorphicTrailingCoeffAt
    have hne1 : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_ne_nhds (by norm_num))
    have heq : chapter04Xi K =ᶠ[𝓝[≠] (0 : ℂ)] f := by
      filter_upwards [self_mem_nhdsWithin, hne1] with z hz0 hz1
      change z ≠ 0 at hz0
      exact chapter04_xi_eq_pole_factor_mul_completed_zeta K z hz0 hz1
    have hlim_xi : Tendsto (chapter04Xi K) (𝓝[≠] (0 : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt f 0)) :=
      Tendsto.congr' heq.symm hlim
    have hcont : ContinuousAt (chapter04Xi K) 0 := by
      apply continuousAt_iff_punctured_nhds.mpr
      rw [hvalue]
      exact hlim_xi
    exact (MeromorphicAt.meromorphicAt_congr heq).2 hf0 |>.analyticAt hcont
  by_cases hs1 : s = 1
  · subst s
    let f : ℂ → ℂ := chapter04PoleFactor * chapter04CompletedDedekindZeta K
    have hpole_an : AnalyticAt ℂ chapter04PoleFactor (1 : ℂ) := by
      unfold chapter04PoleFactor
      fun_prop
    have hpole_mer : MeromorphicAt chapter04PoleFactor (1 : ℂ) :=
      hpole_an.meromorphicAt
    have hzeta_mer : MeromorphicAt (chapter04CompletedDedekindZeta K) (1 : ℂ) :=
      chapter04_completed_dedekind_zeta_meromorphic K 1
    have hf : MeromorphicAt f 1 := by
      exact hpole_mer.mul hzeta_mer
    have hpole_order : meromorphicOrderAt chapter04PoleFactor 1 = (1 : ℤ) := by
      apply (meromorphicOrderAt_eq_int_iff (by fun_prop)).2
      refine ⟨fun z : ℂ => (1 / 2 : ℂ) * z,
        analyticAt_const.mul analyticAt_id, by norm_num, ?_⟩
      filter_upwards [] with z
      simp [chapter04PoleFactor]
      ring_nf
    have horder : meromorphicOrderAt f 1 = 0 := by
      have hmul := meromorphicOrderAt_mul hpole_mer hzeta_mer
      calc
        meromorphicOrderAt f 1 =
            meromorphicOrderAt chapter04PoleFactor 1 +
              meromorphicOrderAt (chapter04CompletedDedekindZeta K) 1 := by
          simpa [f] using hmul
        _ = 0 := by
          rw [hpole_order,
            (chapter04_completed_dedekind_zeta_simple_poles K).2.1]
          norm_num
    have hpole_res : meromorphicTrailingCoeffAt chapter04PoleFactor 1 = (1 / 2 : ℂ) := by
      have hres' :=
        (analyticAt_const.mul analyticAt_id).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
          (f := chapter04PoleFactor) (x := (1 : ℂ))
          (g := fun z : ℂ => (1 / 2 : ℂ) * z) (n := 1) (by norm_num) (by
            filter_upwards [] with z
            simp [chapter04PoleFactor]
            ring_nf)
      simpa using hres'
    have hres : meromorphicTrailingCoeffAt f 1 =
        (1 / 2 : ℂ) * meromorphicTrailingCoeffAt
          (chapter04CompletedDedekindZeta K) 1 := by
      change meromorphicTrailingCoeffAt
        (fun z : ℂ => chapter04PoleFactor z * chapter04CompletedDedekindZeta K z) 1 = _
      rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul hpole_mer hzeta_mer,
        hpole_res]
    have hvalue : chapter04Xi K 1 = meromorphicTrailingCoeffAt f 1 := by
      rw [show chapter04Xi K 1 =
          (Fintype.card (ClassGroup (𝓞 K)) : ℂ) /
            ((2 : ℂ) * (chapter04MellinConstant K
              (chapter04ChosenUnitFundamentalDomain K) : ℂ)) by
            simp [chapter04Xi], hres,
        chapter04_completed_dedekind_zeta_trailing_coeff_at_one K]
      field_simp [chapter04_mellin_constant_ne_zero K
        (chapter04ChosenUnitFundamentalDomain K)]
      
    have hlim : Tendsto f (𝓝[≠] (1 : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt f 1)) := by
      simpa [horder] using hf.tendsto_nhds_meromorphicTrailingCoeffAt
    have hne0 : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_ne_nhds (by norm_num))
    have heq : chapter04Xi K =ᶠ[𝓝[≠] (1 : ℂ)] f := by
      filter_upwards [self_mem_nhdsWithin, hne0] with z hz1 hz0
      change z ≠ 1 at hz1
      exact chapter04_xi_eq_pole_factor_mul_completed_zeta K z hz0 hz1
    have hlim_xi : Tendsto (chapter04Xi K) (𝓝[≠] (1 : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt f 1)) :=
      Tendsto.congr' heq.symm hlim
    have hcont : ContinuousAt (chapter04Xi K) 1 := by
      apply continuousAt_iff_punctured_nhds.mpr
      rw [hvalue]
      exact hlim_xi
    exact (MeromorphicAt.meromorphicAt_congr heq).2 hf |>.analyticAt hcont
  have heq : chapter04Xi K =ᶠ[𝓝 s] (fun z : ℂ =>
      chapter04PoleFactor z * chapter04CompletedDedekindZeta K z) := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact chapter04_xi_eq_pole_factor_mul_completed_zeta K z hz0 hz1
  apply (analyticAt_congr heq).2
  have hq : AnalyticAt ℂ (chapter04ZeroVectorCorrection) s := by
    unfold chapter04ZeroVectorCorrection
    have hden₁ : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
    have hden₀ : AnalyticAt ℂ (fun z : ℂ => z) s := by fun_prop
    exact (analyticAt_const.div hden₁ (sub_ne_zero.mpr hs1)).sub
      (analyticAt_const.div hden₀ hs0)
  have hpartial (C : ClassGroup (𝓞 K)) :
      AnalyticAt ℂ (chapter04CompletedPartialZetaContinuation K
        (chapter04ChosenUnitFundamentalDomain K) C) s := by
    unfold chapter04CompletedPartialZetaContinuation
    change AnalyticAt ℂ (chapter04CompletedPartialZetaForIdeal K
      (chapter04ChosenUnitFundamentalDomain K)
      (chapter04FractionalIdealRepresentative K C⁻¹)) s
    unfold chapter04CompletedPartialZetaForIdeal
    have h₁ := chapter04_theta_mellin_tail_entire K
      (chapter04ChosenUnitFundamentalDomain K)
      (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)) s (Set.mem_univ _)
    have h₂ := chapter04_theta_mellin_tail_entire K
      (chapter04ChosenUnitFundamentalDomain K)
      (chapter04_dual_fractional_ideal_ne_zero K
        (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹))) (1 - s)
        (Set.mem_univ _)
    have h₂' : AnalyticAt ℂ (fun z : ℂ =>
        chapter04ThetaMellinTail K (chapter04ChosenUnitFundamentalDomain K)
          (chapter04DualFractionalIdeal K
            (chapter04FractionalIdealRepresentative K C⁻¹)) (1 - z)) s := by
      simpa [Function.comp_def] using h₂.comp (by fun_prop)
    have hsum : AnalyticAt ℂ (fun z : ℂ =>
        chapter04ThetaMellinTail K (chapter04ChosenUnitFundamentalDomain K)
            (chapter04FractionalIdealRepresentative K C⁻¹) z +
          chapter04ThetaMellinTail K (chapter04ChosenUnitFundamentalDomain K)
            (chapter04DualFractionalIdeal K
              (chapter04FractionalIdealRepresentative K C⁻¹)) (1 - z) +
        chapter04ZeroVectorCorrection z) s := by
      convert (h₁.add h₂').add hq using 1
      funext z
      rfl
    exact analyticAt_const.mul hsum
  have hzeta : AnalyticAt ℂ (chapter04CompletedDedekindZeta K) s := by
    unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
    change AnalyticAt ℂ (fun z : ℂ =>
      ∑' C : ClassGroup (𝓞 K),
        chapter04CompletedPartialZetaContinuation K
          (chapter04ChosenUnitFundamentalDomain K) C z) s
    have hsum : AnalyticAt ℂ
        (∑ C : ClassGroup (𝓞 K), fun z : ℂ =>
          chapter04CompletedPartialZetaContinuation K
            (chapter04ChosenUnitFundamentalDomain K) C z) s := by
      apply Finset.analyticAt_sum Finset.univ
      intro C hC
      exact hpartial C
    have hfun :
        (∑ C : ClassGroup (𝓞 K), fun z : ℂ =>
          chapter04CompletedPartialZetaContinuation K
            (chapter04ChosenUnitFundamentalDomain K) C z) =
          (fun z : ℂ => ∑' C : ClassGroup (𝓞 K),
            chapter04CompletedPartialZetaContinuation K
              (chapter04ChosenUnitFundamentalDomain K) C z) := by
      funext z
      rw [Finset.sum_apply, tsum_fintype]
    rw [← hfun]
    exact hsum
  have hpole : AnalyticAt ℂ chapter04PoleFactor s := by
    unfold chapter04PoleFactor
    fun_prop
  exact hpole.mul hzeta

theorem chapter04_xi_functional_equation
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04Xi K s = chapter04Xi K (1 - s) := by
  by_cases hs0 : s = 0
  · subst s
    simp [chapter04Xi]
  by_cases hs1 : s = 1
  · subst s
    simp [chapter04Xi]
  have hs : ¬ (s = 0 ∨ s = 1) := fun h => h.elim hs0 hs1
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h).symm
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    have h' := congrArg (fun z : ℂ => 1 - z) h
    exact hs0 (by simpa [sub_sub_cancel] using h')
  have h1s : ¬ (1 - s = 0 ∨ 1 - s = 1) := fun h => h.elim h1s0 h1s1
  unfold chapter04Xi
  rw [if_neg hs, if_neg h1s]
  rw [chapter04_completed_dedekind_zeta_functional_equation K s]
  have hpole : chapter04PoleFactor s = chapter04PoleFactor (1 - s) := by
    unfold chapter04PoleFactor
    ring
  rw [hpole, mul_comm]

theorem chapter04_xi_conjugation_symmetry
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04Xi K (star s) = star (chapter04Xi K s) := by
  have hkernel (z : ℂ) {t : ℝ} (ht : 0 < t) :
      chapter04MellinKernel (star z) t = star (chapter04MellinKernel z t) := by
    unfold chapter04MellinKernel
    rw [if_pos ht]
    rw [if_pos ht]
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht.le]
      exact (ne_of_gt Real.pi_pos).symm
    have hcpow : (t : ℂ) ^ (star z) = star ((t : ℂ) ^ z) := by
      have h := Complex.cpow_conj (t : ℂ) z harg
      rw [← Complex.star_def] at h
      have htstar : star (t : ℂ) = (t : ℂ) := by
        rw [Complex.star_def]
        exact Complex.conj_ofReal t
      rw [htstar] at h
      exact h
    rw [hcpow]
    simp
  have htail (a : Chapter04FractionalIdeal K) (z : ℂ) :
      chapter04ThetaMellinTail K (chapter04ChosenUnitFundamentalDomain K) a
          (star z) =
        star (chapter04ThetaMellinTail K
          (chapter04ChosenUnitFundamentalDomain K) a z) := by
    unfold chapter04ThetaMellinTail
    calc
      (∫ t in Set.Ioi (1 : ℝ),
          ((chapter04ThetaAverage K (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
            chapter04MellinKernel (star z) t ∂volume) =
          ∫ t in Set.Ioi (1 : ℝ),
            star (((chapter04ThetaAverage K
              (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
              chapter04MellinKernel z t) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 1 < t at ht
        dsimp
        change ((chapter04ThetaAverage K
            (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
              chapter04MellinKernel (star z) t =
            star (((chapter04ThetaAverage K
              (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
              chapter04MellinKernel z t)
        rw [hkernel z (lt_trans zero_lt_one ht)]
        simp
      _ = star (∫ t in Set.Ioi (1 : ℝ),
          ((chapter04ThetaAverage K (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
            chapter04MellinKernel z t ∂volume) := by
        simpa only [starRingEnd_apply] using
          (integral_conj (μ := volume.restrict (Set.Ioi (1 : ℝ)))
            (f := fun t : ℝ =>
                ((chapter04ThetaAverage K
                (chapter04ChosenUnitFundamentalDomain K) a t - 1 : ℝ) : ℂ) *
                chapter04MellinKernel z t))
  have hcorr (z : ℂ) :
      chapter04ZeroVectorCorrection (star z) =
        star (chapter04ZeroVectorCorrection z) := by
    simp [chapter04ZeroVectorCorrection]
  have hpartial (a : Chapter04NonzeroFractionalIdeal K) (z : ℂ) :
      chapter04CompletedPartialZetaForIdeal K
          (chapter04ChosenUnitFundamentalDomain K) a (star z) =
        star (chapter04CompletedPartialZetaForIdeal K
          (chapter04ChosenUnitFundamentalDomain K) a z) := by
    unfold chapter04CompletedPartialZetaForIdeal
    have harg : 1 - star z = star (1 - z) := by simp
    rw [harg, htail (a : Chapter04FractionalIdeal K) z,
      htail (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K))
        (1 - z), hcorr]
    simp
  have hcont (C : ClassGroup (𝓞 K)) (z : ℂ) :
      chapter04CompletedPartialZetaContinuation K
          (chapter04ChosenUnitFundamentalDomain K) C (star z) =
        star (chapter04CompletedPartialZetaContinuation K
          (chapter04ChosenUnitFundamentalDomain K) C z) := by
    unfold chapter04CompletedPartialZetaContinuation
    exact hpartial _ _
  have hzeta (z : ℂ) :
      chapter04CompletedDedekindZeta K (star z) =
        star (chapter04CompletedDedekindZeta K z) := by
    unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
    rw [tsum_fintype, tsum_fintype]
    change (∑ b : ClassGroup (𝓞 K),
        chapter04CompletedPartialZetaContinuation
          K (chapter04ChosenUnitFundamentalDomain K) b (star z)) =
      starRingEnd ℂ (∑ b : ClassGroup (𝓞 K),
        chapter04CompletedPartialZetaContinuation
          K (chapter04ChosenUnitFundamentalDomain K) b z)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro C hC
    simpa only [starRingEnd_apply] using hcont C z
  by_cases hs0 : s = 0
  · subst s
    simp [chapter04Xi]
  by_cases hs1 : s = 1
  · subst s
    simp [chapter04Xi]
  have hstar0 : star s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg star h
  have hstar1 : star s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg star h
  unfold chapter04Xi
  rw [if_neg (fun h => h.elim hstar0 hstar1),
    if_neg (fun h => h.elim hs0 hs1), hzeta]
  unfold chapter04PoleFactor
  simp

theorem chapter04_xi_not_identically_zero
    (K : Type*) [Field K] [NumberField K] :
    ¬(∀ s : ℂ, chapter04Xi K s = 0) := by
  intro hzero
  have hxi2 : chapter04Xi K (2 : ℂ) ≠ 0 := by
    rw [chapter04Xi,
      chapter04_completed_dedekind_zeta_agrees_on_euler_half_plane K (by norm_num)]
    simp only [chapter04EulerCompletedDedekindZeta, chapter04PoleFactor,
      chapter04ArchimedeanFactor, chapter04GammaReal, chapter04GammaComplex]
    norm_num [Complex.cpow_eq_zero_iff, chapter03_dedekind_zeta_ne_zero]
    exact ⟨(chapter04_absolute_discriminant_pos K).ne',
      chapter03_dedekind_zeta_ne_zero K (by
        change (1 : ℝ) < 2
        norm_num)⟩
  exact hxi2 (hzero 2)

def chapter04NontrivialZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  chapter04Xi K ρ = 0

theorem chapter04_mem_nontrivial_zero_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ {ρ : ℂ | chapter04NontrivialZero K ρ} ↔
      chapter04Xi K ρ = 0 := by
  rfl

noncomputable def chapter04ZeroMultiplicity
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : ℕ :=
  (analyticOrderAt (chapter04Xi K) ρ).toNat

theorem chapter04_zero_multiplicity_pos_iff
    (K : Type*) [Field K] [NumberField K] {ρ : ℂ} :
    0 < chapter04ZeroMultiplicity K ρ ↔ chapter04NontrivialZero K ρ := by
  constructor
  · intro h
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    change (analyticOrderAt (chapter04Xi K) ρ).toNat ≠ 0
    exact Nat.ne_of_gt h
  · intro h
    unfold chapter04NontrivialZero at h
    have hwhole := chapter04_xi_entire K
    have hρ : AnalyticAt ℂ (chapter04Xi K) ρ := hwhole ρ (Set.mem_univ _)
    obtain ⟨z, hz⟩ : ∃ z : ℂ, chapter04Xi K z ≠ 0 := by
      by_contra h'
      push Not at h'
      exact (chapter04_xi_not_identically_zero K) h'
    have hzorder : analyticOrderAt (chapter04Xi K) z ≠ ⊤ := by
      have hzzero : analyticOrderAt (chapter04Xi K) z = 0 :=
        (hwhole z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz
      rw [hzzero]
      exact ENat.zero_ne_top
    have hρtop : analyticOrderAt (chapter04Xi K) ρ ≠ ⊤ :=
      hwhole.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (Set.mem_univ _) (Set.mem_univ _) hzorder
    unfold chapter04ZeroMultiplicity
    exact ENat.toNat_pos (hρ.analyticOrderAt_ne_zero.mpr h) hρtop

def chapter04CriticalStrip (ρ : ℂ) : Prop :=
  0 ≤ ρ.re ∧ ρ.re ≤ 1

theorem chapter04_nontrivial_zero_in_critical_strip
    (K : Type*) [Field K] [NumberField K] {ρ : ℂ}
    (hρ : chapter04NontrivialZero K ρ) :
    chapter04CriticalStrip ρ := by
  unfold chapter04CriticalStrip
  have hnonzero : ∀ z : ℂ, 1 < z.re → chapter04Xi K z ≠ 0 := by
    intro z hz
    have hzpos : 0 < z.re := lt_trans zero_lt_one hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    rw [chapter04_xi_eq_pole_factor_mul_completed_zeta K z hz0 hz1,
      chapter04_completed_dedekind_zeta_agrees_on_euler_half_plane K hz]
    unfold chapter04EulerCompletedDedekindZeta chapter04ArchimedeanFactor
    have hreal : chapter04GammaReal z ≠ 0 := by
      unfold chapter04GammaReal
      apply mul_ne_zero
      · exact Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)))
      · apply Complex.Gamma_ne_zero_of_re_pos
        rw [Complex.div_ofNat_re]
        linarith
    have hcomplex : chapter04GammaComplex z ≠ 0 := by
      unfold chapter04GammaComplex
      apply mul_ne_zero
      · apply Complex.cpow_ne_zero_iff.mpr
        left
        exact mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))
      · exact Complex.Gamma_ne_zero_of_re_pos hzpos
    have harch : chapter04GammaReal z ^ chapter04RealPlaces K *
        chapter04GammaComplex z ^ chapter04ComplexPlaces K ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hreal) (pow_ne_zero _ hcomplex)
    have hdisc : (chapter04AbsoluteDiscriminant K : ℂ) ^ (z / 2) ≠ 0 := by
      apply Complex.cpow_ne_zero_iff.mpr
      left
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (chapter04_absolute_discriminant_pos K))
    have hzeta : chapter03DedekindZeta K z ≠ 0 := by
      apply chapter03_dedekind_zeta_ne_zero K
      exact hz
    have hpole : (1 / 2 : ℂ) * z * (z - 1) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) hz0)
        (sub_ne_zero.mpr hz1)
    exact mul_ne_zero hpole (mul_ne_zero (mul_ne_zero hdisc harch) hzeta)
  constructor
  · by_contra h
    have hleft : ρ.re < 0 := lt_of_not_ge h
    have hpartner : 1 < (1 - ρ).re := by
      norm_num [Complex.sub_re]
      linarith
    have hzero : chapter04Xi K (1 - ρ) = 0 := by
      rw [← chapter04_xi_functional_equation K ρ]
      exact hρ
    have hnotzero : chapter04Xi K (1 - ρ) ≠ 0 :=
      hnonzero (1 - ρ) hpartner
    exact hnotzero hzero
  · by_contra h
    have hright : 1 < ρ.re := lt_of_not_ge h
    have hnotzero : chapter04Xi K ρ ≠ 0 := hnonzero ρ hright
    exact hnotzero hρ

/-- The functional-equation/conjugation partner used by later zero sums. -/
def chapter04ZeroPartner (ρ : ℂ) : ℂ :=
  1 - star ρ

theorem chapter04_nontrivial_zero_partner_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04NontrivialZero K ρ ↔
      chapter04NontrivialZero K (chapter04ZeroPartner ρ) := by
  constructor
  · intro h
    unfold chapter04NontrivialZero at h ⊢
    rw [chapter04ZeroPartner, ← chapter04_xi_functional_equation K (star ρ)]
    rw [chapter04_xi_conjugation_symmetry K ρ, h]
    simp
  · intro h
    unfold chapter04NontrivialZero at h ⊢
    have heq : chapter04Xi K (chapter04ZeroPartner ρ) = star (chapter04Xi K ρ) := by
      rw [chapter04ZeroPartner, ← chapter04_xi_functional_equation K (star ρ)]
      exact chapter04_xi_conjugation_symmetry K ρ
    rw [heq] at h
    simpa using h

theorem chapter04_zero_multiplicity_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04ZeroMultiplicity K (chapter04ZeroPartner ρ) =
      chapter04ZeroMultiplicity K ρ := by
  have hiter : ∀ (f : ℂ → ℂ) (n : ℕ),
      iteratedDeriv n (fun z : ℂ => star (f (star z))) =
        (fun z : ℂ => star (iteratedDeriv n f (star z))) := by
    intro f n
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv :
          deriv (fun z : ℂ => star (f (star z))) =
            (fun z : ℂ => star (deriv f (star z))) := by
        simpa [Function.comp_def] using (deriv_star_conj (f := f))
      rw [hderiv]
      simpa [iteratedDeriv_succ'] using ih (deriv f)
  have hf : AnalyticOnNhd ℂ (chapter04Xi K) Set.univ := chapter04_xi_entire K
  have hfun : (fun z : ℂ => star (chapter04Xi K (star z))) = chapter04Xi K := by
    funext z
    simpa using (chapter04_xi_conjugation_symmetry K (star z)).symm
  have hconj_order (z : ℂ) :
      analyticOrderAt (chapter04Xi K) (star z) =
        analyticOrderAt (chapter04Xi K) z := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf _ (Set.mem_univ _)),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (hf _ (Set.mem_univ _))]
    have hzero (i : ℕ) (w : ℂ) :
        iteratedDeriv i (chapter04Xi K) w = 0 ↔
          iteratedDeriv i (chapter04Xi K) (star w) = 0 := by
      have hderiv :
          iteratedDeriv i (chapter04Xi K) w =
            star (iteratedDeriv i (chapter04Xi K) (star w)) := by
        rw [← hfun]
        have h := congrFun (hiter (chapter04Xi K) i) w
        simpa only [hfun] using h
      rw [hderiv]
      simp
    constructor
    · intro h i hi
      exact (hzero i z).mpr (h i hi)
    · intro h i hi
      exact (hzero i z).mp (h i hi)
  have haffine_order (z : ℂ) :
      analyticOrderAt (chapter04Xi K) (1 - z) =
        analyticOrderAt (chapter04Xi K) z := by
    have hcomp :
        (chapter04Xi K) ∘ (fun w : ℂ => 1 - w) = chapter04Xi K := by
      funext w
      simpa [Function.comp_def] using
        (chapter04_xi_functional_equation K w).symm
    have horder := analyticOrderAt_comp_of_deriv_ne_zero
      (f := chapter04Xi K) (g := fun w : ℂ => 1 - w) (z₀ := z)
      (by fun_prop) (by norm_num)
    rw [hcomp] at horder
    exact horder.symm
  unfold chapter04ZeroMultiplicity
  have horder :
      analyticOrderAt (chapter04Xi K) (chapter04ZeroPartner ρ) =
        analyticOrderAt (chapter04Xi K) ρ := by
    rw [chapter04ZeroPartner]
    calc
      analyticOrderAt (chapter04Xi K) (1 - star ρ) =
          analyticOrderAt (chapter04Xi K) (star ρ) := haffine_order (star ρ)
      _ = analyticOrderAt (chapter04Xi K) ρ := hconj_order ρ
  rw [horder]

theorem chapter04_nontrivial_zero_conjugate_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04NontrivialZero K ρ ↔ chapter04NontrivialZero K (star ρ) := by
  unfold chapter04NontrivialZero
  rw [chapter04_xi_conjugation_symmetry K ρ]
  simp

theorem chapter04_zero_multiplicity_conjugate
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04ZeroMultiplicity K (star ρ) = chapter04ZeroMultiplicity K ρ := by
  have hiter : ∀ (f : ℂ → ℂ) (n : ℕ),
      iteratedDeriv n (fun z : ℂ => star (f (star z))) =
        (fun z : ℂ => star (iteratedDeriv n f (star z))) := by
    intro f n
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv :
          deriv (fun z : ℂ => star (f (star z))) =
            (fun z : ℂ => star (deriv f (star z))) := by
        simpa [Function.comp_def] using (deriv_star_conj (f := f))
      rw [hderiv]
      simpa [iteratedDeriv_succ'] using ih (deriv f)
  have hf : AnalyticOnNhd ℂ (chapter04Xi K) Set.univ := chapter04_xi_entire K
  have hfun : (fun z : ℂ => star (chapter04Xi K (star z))) = chapter04Xi K := by
    funext z
    simpa using (chapter04_xi_conjugation_symmetry K (star z)).symm
  have horder :
      analyticOrderAt (chapter04Xi K) (star ρ) =
        analyticOrderAt (chapter04Xi K) ρ := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf _ (Set.mem_univ _)),
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
        (hf _ (Set.mem_univ _))]
    have hzero (i : ℕ) :
        iteratedDeriv i (chapter04Xi K) (star ρ) = 0 ↔
          iteratedDeriv i (chapter04Xi K) ρ = 0 := by
      have hderiv :
          iteratedDeriv i (chapter04Xi K) ρ =
            star (iteratedDeriv i (chapter04Xi K) (star ρ)) := by
        rw [← hfun]
        have h := congrFun (hiter (chapter04Xi K) i) ρ
        simpa only [hfun] using h
      rw [hderiv]
      simp
    constructor
    · intro h i hi
      exact (hzero i).mp (h i hi)
    · intro h i hi
      exact (hzero i).mpr (h i hi)
  unfold chapter04ZeroMultiplicity
  rw [horder]

/- The boundary-line statement is deliberately an interface for the separate
   zero-free-line theorem mentioned in the source, not an unproved theorem of
   this chapter. -/
def chapter04BoundaryZeroFree
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ ρ : ℂ, chapter04NontrivialZero K ρ →
    (ρ.re = 0 ∨ ρ.re = 1) → False

/-- The aggregate archimedean factor whose poles are canceled by trivial zeros. -/
noncomputable def chapter04ArchimedeanLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  deriv (chapter04ArchimedeanFactor K) s /
    chapter04ArchimedeanFactor K s

def chapter04GammaPoleSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | meromorphicOrderAt (chapter04ArchimedeanFactor K) s < 0}

def chapter04TrivialZeroSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | s ∈ chapter04GammaPoleSet K ∧
    s ≠ 0 ∧ chapter04DedekindZetaContinuation K s = 0}

theorem chapter04_gamma_poles_away_from_zero_are_canceled_by_trivial_zeros
    (K : Type*) [Field K] [NumberField K] :
    (chapter04GammaPoleSet K \ {0}) ⊆
      {s : ℂ | chapter04DedekindZetaContinuation K s = 0} := by
  intro s hs
  exact chapter04_dedekind_zeta_zero_of_archimedean_pole K hs.2 hs.1

theorem chapter04_trivial_zero_set_mem_gamma_poles
    (K : Type*) [Field K] [NumberField K] :
    chapter04TrivialZeroSet K ⊆ chapter04GammaPoleSet K := by
  intro s hs
  exact hs.1

theorem chapter04_trivial_zero_contribution_is_aggregate
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04ArchimedeanLogDerivative K s =
      deriv (chapter04ArchimedeanFactor K) s /
        chapter04ArchimedeanFactor K s := by
  rfl

theorem chapter04_pole_factor_log_derivative
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv chapter04PoleFactor s / chapter04PoleFactor s =
      1 / s + 1 / (s - 1) := by
  have hderiv :
      HasDerivAt chapter04PoleFactor
        ((1 / 2 : ℂ) * (s - 1) + (1 / 2 : ℂ) * s) s := by
    change HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1))
      ((1 / 2 : ℂ) * (s - 1) + (1 / 2 : ℂ) * s) s
    convert (((hasDerivAt_const s (1 / 2 : ℂ)).mul (hasDerivAt_id s)).mul
      ((hasDerivAt_id s).sub (hasDerivAt_const s (1 : ℂ)))) using 1
    · rfl
    · rfl
    · funext z
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
      ring
  rw [hderiv.deriv]
  simp only [chapter04PoleFactor]
  field_simp [hs0, hs1]

noncomputable def chapter04ResidueAt
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  meromorphicTrailingCoeffAt f z

theorem chapter04_residues_at_zero_and_one_are_opposite
    (K : Type*) [Field K] [NumberField K] :
    chapter04ResidueAt (chapter04CompletedDedekindZeta K) 0 =
      -chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1 := by
  let f : ℂ → ℂ := chapter04CompletedDedekindZeta K
  let g : ℂ → ℂ := fun z => 1 - z
  have hf : Meromorphic f := by
    exact chapter04_completed_dedekind_zeta_meromorphic K
  have horder : meromorphicOrderAt f 1 = (-1 : ℤ) := by
    exact (chapter04_completed_dedekind_zeta_simple_poles K).2.1
  have hcomp : f ∘ g = f := by
    funext z
    exact (chapter04_completed_dedekind_zeta_functional_equation K z).symm
  have hg : AnalyticAt ℂ g 0 := by
    fun_prop
  have hg_nc : ¬EventuallyConst g (nhds (0 : ℂ)) := by
    simp only [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    have hneg : analyticOrderAt (fun z : ℂ => -z) 0 = (1 : ℕ∞) := by
      apply (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0).analyticOrderAt_eq_natCast.mpr
      refine ⟨fun _ => (-1 : ℂ), by fun_prop, by norm_num, ?_⟩
      filter_upwards [] with z
      simp
    rw [show (g · - g 0) = (fun z : ℂ => -z) by
      funext z
      simp [g], hneg]
    exact ENat.one_ne_top
  have hfactor :
      meromorphicTrailingCoeffAt (g · - g 0) (0 : ℂ) = (-1 : ℂ) := by
    have hfun : (g · - g 0) = -(fun z : ℂ => z) := by
      funext z
      simp [g]
    rw [hfun, meromorphicTrailingCoeffAt_neg]
    have hid : meromorphicTrailingCoeffAt (fun z : ℂ => z) (0 : ℂ) = (1 : ℂ) := by
      simpa using
        (meromorphicTrailingCoeffAt_id_sub_const (x := (0 : ℂ)) (y := (0 : ℂ)))
    rw [hid]
  have hcomp_coeff :=
    MeromorphicAt.meromorphicTrailingCoeffAt_comp
      (f := f) (x := (0 : ℂ)) (g := g)
      (by simpa [g] using hf 1) hg hg_nc
  change meromorphicTrailingCoeffAt f 0 =
    -meromorphicTrailingCoeffAt f 1
  calc
    meromorphicTrailingCoeffAt f 0 =
        meromorphicTrailingCoeffAt (f ∘ g) 0 := by rw [hcomp]
    _ = meromorphicTrailingCoeffAt (g · - g 0) 0 ^
          (meromorphicOrderAt f (g 0)).untop₀ •
          meromorphicTrailingCoeffAt f (g 0) := hcomp_coeff
    _ = -meromorphicTrailingCoeffAt f 1 := by
      rw [hfactor, show g 0 = 1 by simp [g], horder]
      norm_num

theorem chapter04_residue_at_one_is_positive_real
    (K : Type*) [Field K] [NumberField K] :
    0 < (chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1).re ∧
      (chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1).im = 0 := by
  classical
  let D := chapter04ChosenUnitFundamentalDomain K
  let scale : ℂ := (chapter04MellinConstant K D : ℂ)⁻¹
  let q : ℂ → ℂ := chapter04ZeroVectorCorrection
  let p : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04ThetaMellinTail K D
        (chapter04FractionalIdealRepresentative K C⁻¹) z +
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K
          (chapter04FractionalIdealRepresentative K C⁻¹ :
            Chapter04FractionalIdeal K)) (1 - z)
  let f : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04CompletedPartialZetaContinuation K D C z
  let P : ℂ → ℂ := fun z =>
    ∑ C : ClassGroup (𝓞 K), scale * p C z
  let c : ℂ := (Fintype.card (ClassGroup (𝓞 K)) : ℂ) * scale
  have hscale : scale ≠ 0 := by
    simp [scale, chapter04_mellin_constant_ne_zero K D]
  have hdecomp (C : ClassGroup (𝓞 K)) :
      f C = fun z => scale * (p C z + q z) := by
    funext z
    simp [f, p, q, scale, D, chapter04CompletedPartialZetaContinuation,
      chapter04CompletedPartialZetaForIdeal]
  have hp (C : ClassGroup (𝓞 K)) (z : ℂ) :
      AnalyticAt ℂ (p C) z := by
    apply (chapter04_theta_mellin_tail_entire K D
      (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)) z
      (Set.mem_univ _)).add
    simpa [p, Function.comp_def] using
      ((chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K
          (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)))
        (1 - z) (Set.mem_univ _)).comp (by fun_prop))
  have hP (z : ℂ) : AnalyticAt ℂ P z := by
    have hsum : AnalyticAt ℂ
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) z := by
      apply Finset.analyticAt_sum Finset.univ
      intro C hC
      exact analyticAt_const.mul (hp C z)
    have hfun :
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) = P := by
      funext w
      rw [Finset.sum_apply]
    rw [← hfun]
    exact hsum
  have hq_order : meromorphicOrderAt q 1 = (-1 : ℤ) := by
    unfold q chapter04ZeroVectorCorrection
    change meromorphicOrderAt
      ((fun z : ℂ => (1 : ℂ) / (z - 1)) +
        (fun z : ℂ => -(1 / z))) 1 = (-1 : ℤ)
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 1 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 1)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun z : ℂ => z) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun z : ℂ => 1 / z) (x := 1)).symm.trans h₂
      change meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 at hneg
      exact hneg
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_left
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  have hq_mer : MeromorphicAt q 1 := by
    change MeromorphicAt (fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z) 1
    fun_prop
  have hq_res : meromorphicTrailingCoeffAt q 1 = (1 : ℂ) := by
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 1 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 1)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun z : ℂ => z) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have hleft :
        meromorphicTrailingCoeffAt
            (fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z) 1 =
          meromorphicTrailingCoeffAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 := by
      exact MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
        (f₁ := fun z : ℂ => (1 : ℂ) / (z - 1))
        (f₂ := fun z : ℂ => (1 : ℂ) / z) (by fun_prop) (by
          rw [h₁, h₂]
          exact WithTop.coe_lt_coe.mpr (by norm_num))
    rw [show q = fun z : ℂ => (1 : ℂ) / (z - 1) - 1 / z by
      funext z
      rfl, hleft]
    have hlin : meromorphicTrailingCoeffAt (fun z : ℂ => z - 1) 1 = (1 : ℂ) := by
      simpa using
        (meromorphicTrailingCoeffAt_id_sub_const (x := (1 : ℂ)) (y := (1 : ℂ)))
    have hinv : meromorphicTrailingCoeffAt (fun z : ℂ => (z - 1)⁻¹) 1 = (1 : ℂ) := by
      rw [meromorphicTrailingCoeffAt_fun_inv, hlin]
      norm_num
    simpa only [one_div] using hinv
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ClassGroup (𝓞 K)) ≠ 0)
    · exact hscale
  have hsecond_mer : MeromorphicAt (fun z : ℂ => c * q z) 1 := by
    change MeromorphicAt
      (fun z : ℂ => c * ((1 : ℂ) / (z - 1) - 1 / z)) 1
    fun_prop
  have hsecond_order :
      meromorphicOrderAt (fun z : ℂ => c * q z) 1 = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun _ : ℂ => c) * q) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_mul_of_ne_zero (by fun_prop) hc, hq_order]
  have hdecomp_sum (z : ℂ) :
      chapter04CompletedDedekindZeta K z = P z + c * q z := by
    unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
    rw [tsum_fintype]
    change (∑ C : ClassGroup (𝓞 K), f C z) = _
    simp_rw [hdecomp]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    change (∑ C : ClassGroup (𝓞 K), scale * p C z) +
        (∑ C : ClassGroup (𝓞 K), scale * q z) = P z + c * q z
    rw [show (∑ C : ClassGroup (𝓞 K), scale * p C z) = P z by rfl]
    congr 1
    rw [← Finset.sum_mul]
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [c, mul_assoc]
  have hdecomp_fun :
      chapter04CompletedDedekindZeta K =
        (fun z => P z + c * q z) := by
    funext z
    exact hdecomp_sum z
  have hres_total :
      meromorphicTrailingCoeffAt (chapter04CompletedDedekindZeta K) 1 =
        meromorphicTrailingCoeffAt (fun z : ℂ => c * q z) 1 := by
    rw [hdecomp_fun]
    change meromorphicTrailingCoeffAt
      ((fun z : ℂ => P z) + (fun z : ℂ => c * q z)) 1 = _
    have hcomm :
        (fun z : ℂ => P z) + (fun z : ℂ => c * q z) =
          (fun z : ℂ => c * q z) + (fun z : ℂ => P z) := by
      funext z
      simp [add_comm]
    rw [hcomm]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt
      (hP 1).meromorphicAt
    rw [hsecond_order]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num))
      (hP 1).meromorphicOrderAt_nonneg
  have hres_scaled :
      meromorphicTrailingCoeffAt (fun z : ℂ => c * q z) 1 =
        c * meromorphicTrailingCoeffAt q 1 := by
    simpa only [Pi.mul_apply, meromorphicTrailingCoeffAt_const] using
      (MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
        (f₁ := fun _ : ℂ => c) (f₂ := q) (by fun_prop) hq_mer)
  change 0 < (meromorphicTrailingCoeffAt
      (chapter04CompletedDedekindZeta K) 1).re ∧
    (meromorphicTrailingCoeffAt
      (chapter04CompletedDedekindZeta K) 1).im = 0
  rw [hres_total, hres_scaled, hq_res]
  dsimp [c, scale]
  have hpos : 0 < chapter04MellinConstant K D :=
    chapter04_mellin_constant_pos K D
  constructor
  · simp [Complex.mul_re]
    positivity
  · simp

/-! The order-one growth interface and the symmetric zero count. -/

def chapter04OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ →
      ‖f z‖ ≤ Real.exp (C * Real.rpow ‖z‖ (1 + ε))

/- The source only needs the order-one upper-growth interface.  Exact lower
   order is stronger and is not part of the continuation argument. -/
def chapter04OrderOne (f : ℂ → ℂ) : Prop :=
  chapter04OrderAtMostOne f

theorem chapter04_xi_order_one
    (K : Type*) [Field K] [NumberField K] :
    chapter04OrderOne (chapter04Xi K) := by
  sorry

theorem chapter04_xi_order_at_most_one
    (K : Type*) [Field K] [NumberField K] :
    chapter04OrderAtMostOne (chapter04Xi K) := by
  exact chapter04_xi_order_one K

def chapter04ZeroBand
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Set ℂ :=
  {ρ | chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T}

theorem chapter04_zero_band_finite
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    (chapter04ZeroBand K T).Finite := by
  have hcont : Continuous (chapter04Xi K) :=
    (chapter04_xi_entire K).continuous
  have hclosed : IsClosed (chapter04ZeroBand K T) := by
    have hz : IsClosed {ρ : ℂ | chapter04NontrivialZero K ρ} := by
      change IsClosed ((chapter04Xi K) ⁻¹' ({0} : Set ℂ))
      exact isClosed_singleton.preimage hcont
    have hi : IsClosed {ρ : ℂ | |ρ.im| ≤ T} := by
      exact isClosed_Iic.preimage (continuous_abs.comp Complex.continuous_im)
    change IsClosed
      ({ρ : ℂ | chapter04NontrivialZero K ρ} ∩ {ρ : ℂ | |ρ.im| ≤ T})
    exact hz.inter hi
  have hbounded : Bornology.IsBounded (chapter04ZeroBand K T) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨1 + |T|, ?_⟩
    intro ρ hρ
    have hstrip := chapter04_nontrivial_zero_in_critical_strip K hρ.1
    have hre : |ρ.re| ≤ 1 := by
      rw [abs_of_nonneg hstrip.1]
      exact hstrip.2
    have him : |ρ.im| ≤ |T| := hρ.2.trans (le_abs_self T)
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im ρ).trans
      (add_le_add hre him)
  have hcompact : IsCompact (chapter04ZeroBand K T) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩
  have hzero_discrete :
      IsDiscrete {ρ : ℂ | chapter04NontrivialZero K ρ} := by
    obtain ⟨z, hz⟩ := not_forall.mp (chapter04_xi_not_identically_zero K)
    have hcodiscrete :
        (chapter04Xi K) ⁻¹' ({0}ᶜ : Set ℂ) ∈ Filter.codiscrete ℂ :=
      (chapter04_xi_entire K).preimage_zero_mem_codiscrete hz
    have h := isDiscrete_of_codiscreteWithin
      (U := (Set.univ : Set ℂ))
      (s := {ρ : ℂ | chapter04NontrivialZero K ρ}) (by
        rw [show ({ρ : ℂ | chapter04NontrivialZero K ρ})ᶜ =
          (chapter04Xi K) ⁻¹' ({0}ᶜ : Set ℂ) by
            ext ρ
            simp [chapter04NontrivialZero]]
        simpa [Filter.codiscrete] using hcodiscrete)
    simpa using h
  exact hcompact.finite (hzero_discrete.mono (by
    intro ρ hρ
    exact hρ.1))

noncomputable def chapter04ZeroCounting
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℕ :=
  (chapter04_zero_band_finite K T).toFinset.sum
    (fun ρ => chapter04ZeroMultiplicity K ρ)

theorem chapter04_zero_counting_monotone
    (K : Type*) [Field K] [NumberField K] {S T : ℝ}
    (hST : S ≤ T) :
    chapter04ZeroCounting K S ≤ chapter04ZeroCounting K T := by
  let fS := chapter04_zero_band_finite K S
  let fT := chapter04_zero_band_finite K T
  have hsubset : chapter04ZeroBand K S ⊆ chapter04ZeroBand K T := by
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.trans hST⟩
  have hfin : fS.toFinset ⊆ fT.toFinset := by
    exact (Set.Finite.toFinset_subset_toFinset).2 hsubset
  change fS.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) ≤
    fT.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hfin
    (fun _ _ _ => Nat.zero_le _)

theorem chapter04_zero_counting_unit_band_bound
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ (K : Type*) [Field K] [NumberField K],
          ((chapter04ZeroCounting K (T + 1) - chapter04ZeroCounting K T : ℕ) : ℝ) ≤
            C * (Real.log (chapter04AbsoluteDiscriminant K) +
              (chapter04Degree K : ℝ) * Real.log (T + 3)) := by
  sorry

/-!
The contour argument in the next chapter needs one additional piece of
analytic bookkeeping.  It is kept here as a conductor-parametrized
interface: Section 4.4 must not depend on the later Section 4.5 definition of
the analytic conductor, while later chapters can specialize `Q` to that
definition by the displayed conductor identity.
-/

def chapter04VerticalLinePoint (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

noncomputable def chapter04LogDerivative (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  deriv f s / f s

/--
An inverse-polynomially separated sequence of contour heights for a
meromorphic logarithmic derivative.  The support and conductor are explicit
parameters so that this interface can be reused by a later contour chapter
without importing that chapter back into Chapter 4.
-/
structure Chapter04ContourHeightSequence
    (f : ℂ → ℂ) (zeroSupport : Set ℂ) (Q : ℝ → ℝ) (c : ℝ) where
  height : ℕ → ℝ
  tendsToInfinity : Tendsto height atTop atTop
  positive : ∀ j, 0 < height j
  conductorPos : ∀ t, 0 < Q t
  separationExponent : ℕ
  separationExponent_ge_two : 2 ≤ separationExponent
  separationConstant : ℝ
  separationConstant_pos : 0 < separationConstant
  avoids_zero_ordinates :
    ∀ (j : ℕ) (ρ : ℂ), ρ ∈ zeroSupport →
      separationConstant /
          Real.rpow (height j + 3) (separationExponent : ℝ) ≤
        |height j - ρ.im|
  logDerivativeBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (σ : ℝ),
      1 - c ≤ σ →
      σ ≤ c →
      ‖chapter04LogDerivative f
          (chapter04VerticalLinePoint σ (height j))‖ ≤
        C * (height j + 3) ^ separationExponent *
            (Real.log (Q (height j))) ^ 2 ∧
      ‖chapter04LogDerivative f
          (chapter04VerticalLinePoint σ (-height j))‖ ≤
        C * (height j + 3) ^ separationExponent *
            (Real.log (Q (height j))) ^ 2

/--
The order-one and unit-band estimates provide the contour-height package for
the completed zeta function.  The conductor equation is an explicit
hypothesis so this theorem remains in Section 4.4; Section 4.5 supplies the
canonical specialization.
-/
theorem chapter04_xi_contour_height_sequence_exists
    (K : Type*) [Field K] [NumberField K]
    {Q : ℝ → ℝ}
    (hQ : ∀ t : ℝ,
      Q t = chapter04AbsoluteDiscriminant K *
        Real.rpow (|t| + 3) (chapter04Degree K : ℝ))
    {c : ℝ} (hc : 1 < c) :
    Nonempty (Chapter04ContourHeightSequence
      (chapter04Xi K) (chapter04NontrivialZero K) Q c) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
