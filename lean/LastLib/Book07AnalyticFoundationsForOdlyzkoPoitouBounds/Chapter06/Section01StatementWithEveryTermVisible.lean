import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
open MeasureTheory Set NumberField
open scoped BigOperators ComplexConjugate

variable {K : Type*} [Field K] [NumberField K]

/-! ### 6.1. Statement with every term visible -/

structure Chapter06ExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) where
  basicAdmissible : Chapter06BasicallyAdmissible F
  zeroContribution : ℝ
  primeContribution : ℝ
  identity :
    Real.log (chapter06AbsoluteDiscriminant K) =
      (chapter06Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        4 * chapter06A F -
        (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F +
        zeroContribution + primeContribution

@[simp] theorem chapter06_degree_def :
    chapter06Degree K = Module.finrank ℚ K :=
  rfl

@[simp] theorem chapter06_real_places_def :
    chapter06RealPlaces K = NumberField.InfinitePlace.nrRealPlaces K :=
  rfl

@[simp] theorem chapter06_complex_places_def :
    chapter06ComplexPlaces K = NumberField.InfinitePlace.nrComplexPlaces K :=
  rfl

@[simp] theorem chapter06_absolute_discriminant_def :
    chapter06AbsoluteDiscriminant K = |(NumberField.discr K : ℝ)| :=
  rfl

theorem chapter06_signature_degree :
    chapter06RealPlaces K + 2 * chapter06ComplexPlaces K = chapter06Degree K := by
  exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

theorem chapter06_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter06AbsoluteDiscriminant K := by
  exact chapter02_absolute_discriminant_pos K

theorem chapter06_root_discriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter06RootDiscriminant K = NumberField.rootDiscr K := by
  simpa [chapter06RootDiscriminant, chapter06AbsoluteDiscriminant, chapter06Degree,
    chapter02RootDiscriminant, chapter02AbsoluteDiscriminant, chapter02Degree] using
    (NumberField.rootDiscr_def K).symm

@[simp] theorem chapter06_phi_eq_centered_laplace
    (F : ℝ → ℝ) (s : ℂ) :
    chapter06Phi F s =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform
        F s :=
  rfl

theorem chapter06_basic_admissible_integrals_convergent
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    IntegrableOn (fun x : ℝ => F x * Real.cosh (x / 2)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2))) (Ioi 0) := by
  rcases hF with ⟨heven, hcont, hcompact, hpiece, hderiv, hF0, hnear0⟩
  have hnear : IntegrableOn (fun x : ℝ => |1 - F x| / x) (Ioc (0 : ℝ) 1) :=
    (chapter05_origin_condition_iff_integrableOn hcont).mp hnear0
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

theorem chapter06_zero_contribution_is_real
    {K : Type*} [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    (chapter06SymmetricZeroSum P.zeros F).im = 0 := by
  let f : ℂ → ℂ := fun ρ => chapter06ZeroSummand P.zeros F ρ
  let e : ℂ ≃ ℂ :=
    { toFun := star
      invFun := star
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  have hs : Summable f := by
    simpa only [f] using chapter06_zero_summand_summable_of_basic K P.zeros hF
  have hse : Summable (fun ρ : ℂ => f (e ρ)) := by
    exact e.summable_iff.mpr hs
  have hphi_star : ∀ s : ℂ,
      chapter06Phi F (star s) = star (chapter06Phi F s) := by
    intro s
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    have hconj :=
      (integral_conj (μ := (volume : Measure ℝ))
        (f := fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x))
    calc
      (∫ x : ℝ, (F x : ℂ) * chapter05LaplaceKernel (star s) x) =
          ∫ x : ℝ, star ((F x : ℂ) * chapter05LaplaceKernel s x) := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp only [chapter05LaplaceKernel]
            rw [star_mul]
            change (F x : ℂ) * Complex.exp ((star s - 1 / 2) * (x : ℂ)) =
              conj (Complex.exp ((s - 1 / 2) * (x : ℂ))) *
                conj (F x : ℂ)
            rw [← Complex.exp_conj, Complex.conj_ofReal]
            have harg : (star s - 1 / 2) * (x : ℂ) =
                conj ((s - 1 / 2) * (x : ℂ)) := by
              change (star s - (1 / 2 : ℂ)) * (x : ℂ) =
                star ((s - 1 / 2) * (x : ℂ))
              rw [star_mul, star_sub]
              have hx : star (x : ℂ) = (x : ℂ) := by
                change conj (x : ℂ) = (x : ℂ)
                exact Complex.conj_ofReal x
              have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
                rw [star_div₀]
                simp
              rw [hx, hhalf]
              ring
            rw [harg]
            ring
      _ = star (∫ x : ℝ, (F x : ℂ) * chapter05LaplaceKernel s x) := hconj
  have hfe : ∀ ρ : ℂ, f (e ρ) = star (f ρ) := by
    intro ρ
    dsimp [f, e]
    change (P.zeros.multiplicity (star ρ) : ℂ) * chapter06Phi F (star ρ) =
      star ((P.zeros.multiplicity ρ : ℂ) * chapter06Phi F ρ)
    rw [P.zeros.multiplicity_conjugation_partner, hphi_star]
    simp
  have hsum : (∑' ρ : ℂ, f ρ) = (∑' ρ : ℂ, f (e ρ)) := by
    exact (e.tsum_eq f).symm
  have hstar_sum : (∑' ρ : ℂ, f (e ρ)) = star (∑' ρ : ℂ, f ρ) := by
    calc
      (∑' ρ : ℂ, f (e ρ)) = ∑' ρ : ℂ, star (f ρ) := by
        congr 1
        funext ρ
        exact hfe ρ
      _ = star (∑' ρ : ℂ, f ρ) := by
        simpa using (tsum_star (f := f)).symm
  have hsum_eq : (∑' ρ : ℂ, f ρ) = star (∑' ρ : ℂ, f ρ) := by
    exact hsum.trans hstar_sum
  have him : (∑' ρ : ℂ, f ρ).im = 0 := by
    have hcoord := congrArg Complex.im hsum_eq
    have hcoord' : (∑' ρ : ℂ, f ρ).im =
        -(∑' ρ : ℂ, f ρ).im := by
      simpa using hcoord
    have hzero : 2 * (∑' ρ : ℂ, f ρ).im = 0 := by
      linarith [hcoord']
    linarith
  simpa [f, chapter06SymmetricZeroSum] using him

theorem chapter06_prime_power_support_finite
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    (chapter06PrimePowerSupport (K := K) F).Finite := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      hF.compactSupport.isBounded with ⟨R, hR⟩
  let T : ℝ := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  have hFsupport : chapter06SupportWithin F T := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) R :=
      hR (subset_closure hx)
    have habs : |x| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx'
    have habsT : |x| ≤ T := habs.trans (le_max_left _ _)
    exact abs_le.mp habsT
  let B : ℕ := Nat.ceil (Real.exp T)
  let M : ℕ := Nat.ceil (T / Real.log (2 : ℝ))
  let S : Set (Chapter06PrimeIdeal K) :=
    {P | chapter06PrimeIdealNorm P ≤ B}
  let U : Set Chapter06PositiveExponent :=
    {m | m.1 ≤ M}
  have hS : S.Finite := by
    simpa [S, B, chapter06PrimeIdealNorm, chapter03PrimeIdealNorm,
      chapter03AbsoluteIdealNorm] using
      (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
        (R := 𝓞 K) B)
  have hU : U.Finite := by
    simpa [U] using
      (Set.finite_le_nat M).preimage (by
        intro a _ b _ hab
        exact Subtype.ext hab)
  have hprod : (S ×ˢ U).Finite := hS.prod hU
  refine hprod.subset ?_
  intro q hq
  change q.1 ∈ S ∧ q.2 ∈ U
  have hterm : chapter06PrimePowerTerm F q ≠ 0 := hq
  have hNgt : 1 < chapter06PrimeIdealNorm q.1 :=
    chapter03_prime_ideal_norm_gt_one q.1
  have hlog : 0 < Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast hNgt)
  have hFq : F ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ≠ 0 := by
    intro hzero
    apply hterm
    simp [chapter06PrimePowerTerm, hzero]
  have hmem : ((q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ∈ Function.support F := hFq
  have hbound : (q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T :=
    hFsupport hmem |>.2
  have hone : (1 : ℝ) ≤ (q.2.1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr q.2.2)
  have hlog_le : Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T := by
    have hmul : Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤
        (q.2.1 : ℝ) * Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone (le_of_lt hlog))
    exact hmul.trans hbound
  have hNreal : (chapter06PrimeIdealNorm q.1 : ℝ) ≤ Real.exp T :=
    Real.le_exp_of_log_le hlog_le
  have hNnat : chapter06PrimeIdealNorm q.1 ≤ B := by
    have hceil : Real.exp T ≤ (B : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hNreal.trans hceil
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ chapter06PrimeIdealNorm q.1 := by
    have hN2nat : 2 ≤ chapter06PrimeIdealNorm q.1 := by
      omega
    exact_mod_cast hN2nat
  have hlog2_le : Real.log (2 : ℝ) ≤
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ) :=
    Real.log_le_log (by norm_num) hN2
  have hprod_bound : (q.2.1 : ℝ) * Real.log (2 : ℝ) ≤ T := by
    exact (mul_le_mul_of_nonneg_left hlog2_le (by positivity)).trans hbound
  have hdiv : (q.2.1 : ℝ) ≤ T / Real.log (2 : ℝ) := by
    exact (le_div_iff₀ hlog2).2 hprod_bound
  have hnat : q.2.1 ≤ M := by
    have hceil : T / Real.log (2 : ℝ) ≤ (M : ℝ) := by
      exact Nat.le_ceil _
    exact_mod_cast hdiv.trans hceil
  exact ⟨hNnat, hnat⟩

noncomputable def chapter06PrimePowerLedger
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ)
    (hF : Chapter06BasicallyAdmissible F) : Finset (Chapter06PrimePower K) :=
  (chapter06_prime_power_support_finite K hF).toFinset

theorem chapter06_mem_prime_power_ledger_iff
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) (q : Chapter06PrimePower K) :
    q ∈ chapter06PrimePowerLedger K F hF ↔
      chapter06PrimePowerTerm F q ≠ 0 := by
  simp [chapter06PrimePowerLedger, chapter06PrimePowerSupport]

theorem chapter06_prime_contribution_eq_ledger_sum
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    chapter06PrimeContribution K F =
      2 * ∑ q ∈ chapter06PrimePowerLedger K F hF,
        chapter06PrimePowerTerm F q := by
  unfold chapter06PrimeContribution
  rw [tsum_eq_sum (s := chapter06PrimePowerLedger K F hF) (by
    intro q hq
    by_contra hq0
    apply hq
    exact (chapter06_mem_prime_power_ledger_iff (K := K) hF q).2 hq0)]

theorem chapter06_prime_contribution_eq_nested_sum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ)
    (hF : Chapter06BasicallyAdmissible F) :
    chapter06PrimeContribution K F =
      2 * ∑' P : Chapter06PrimeIdeal K,
        ∑' m : Chapter06PositiveExponent, chapter06PrimePowerTerm F (P, m) := by
  have hsum : Summable (fun q : Chapter06PrimePower K =>
      chapter06PrimePowerTerm F q) := by
    apply summable_of_hasFiniteSupport
    change Set.Finite {q : Chapter06PrimePower K |
      chapter06PrimePowerTerm F q ≠ 0}
    exact chapter06_prime_power_support_finite K hF
  unfold chapter06PrimeContribution
  rw [hsum.tsum_prod]

/-
Chapter 4 supplies the canonical completed-zeta and zero data.  The package
parametrization below remains useful for the contour proof, while
`chapter06CanonicalZetaAnalyticPackage` exposes that canonical analytic core;
the Chapter 6 explicit formula remains a statement proved separately.
-/
theorem chapter06_weil_poitou_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Real.log (chapter06AbsoluteDiscriminant K) =
      chapter06ExplicitFormulaRightHandSide K P.zeros F := by
  exact chapter06_weil_poitou_explicit_formula_bridge K P hF

theorem chapter06_weil_poitou_explicit_formula_canonical
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Real.log (chapter06AbsoluteDiscriminant K) =
      chapter06ExplicitFormulaRightHandSide K
        (chapter06CanonicalZetaAnalyticPackage K).zeros F := by
  exact chapter06_weil_poitou_explicit_formula K
    (chapter06CanonicalZetaAnalyticPackage K) hF

theorem chapter06_weil_poitou_explicit_formula_expanded
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Real.log (chapter06AbsoluteDiscriminant K) =
      (chapter06Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        4 * chapter06A F -
        (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F +
        chapter06ZeroContribution P.zeros F + chapter06PrimeContribution K F := by
  exact chapter06_weil_poitou_explicit_formula K P hF

noncomputable def chapter06CanonicalExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Chapter06ExplicitFormulaData K F :=
  { basicAdmissible := hF
    zeroContribution :=
      chapter06ZeroContribution
        (chapter06CanonicalZetaAnalyticPackage K).zeros F
    primeContribution := chapter06PrimeContribution K F
    identity :=
      chapter06_weil_poitou_explicit_formula_expanded K
        (chapter06CanonicalZetaAnalyticPackage K) hF }

noncomputable def chapter06CanonicalUnconditionalExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06UnconditionallyAdmissible F) :
    Chapter06ExplicitFormulaData K F :=
  chapter06CanonicalExplicitFormulaData K hF.1

noncomputable def chapter06CanonicalGRHExplicitFormulaData
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06GRHAdmissible F) :
    Chapter06ExplicitFormulaData K F :=
  chapter06CanonicalExplicitFormulaData K hF.basic

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
