import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set Filter NumberField Topology
open scoped BigOperators Topology ContDiff Pointwise
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

/-! ### 6.5. Removing the truncations -/

theorem chapter06_basic_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
 exact chapter06_zero_summand_summable_of_basic K Z hF
theorem chapter06_canonical_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter05_symmetric_zero_sum_summable K hF

theorem chapter06_canonical_unconditional_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06UnconditionallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter06_canonical_zero_summand_summable K hF.1

theorem chapter06_canonical_grh_zero_summand_summable
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06GRHAdmissible F) :
    Summable (fun ρ : ℂ =>
      chapter06ZeroSummand
        (chapter06CanonicalZetaAnalyticPackage K).zeros F ρ) := by
  exact chapter06_canonical_zero_summand_summable K hF.basic

theorem chapter06_zero_count_unit_band
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter06ZeroBandCount Z T : ℕ) : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  exact Z.unit_band_bound

theorem chapter06_zero_count_increment_bound
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      (chapter06ZeroBandCount Z T : ℝ) ≤
        C * (Real.log (chapter06AbsoluteDiscriminant K) +
          (chapter06Degree K : ℝ) * Real.log (T + 3)) := by
  exact chapter06_zero_count_unit_band K Z

private theorem chapter06_smooth_compact_basic_of_value_at_zero_early
    {G : ℝ → ℝ} (hG : Chapter06SmoothCompactSupport G) (hG0 : G 0 = 1) :
    Chapter06BasicallyAdmissible G := by
  rcases hG with ⟨hGeven, hGdiff, hGcompact⟩
  have hGderivDiff : Differentiable ℝ (deriv G) := by
    exact (contDiff_infty_iff_deriv.mp hGdiff).2.differentiable (by simp)
  have hGderivDerivCont : Continuous (deriv (deriv G)) := by
    have hGderivDeriv : ContDiff ℝ ∞ (deriv (deriv G)) := by
      exact (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp hGdiff).2).2
    exact hGderivDeriv.continuous
  have hGderivDerivCompact : HasCompactSupport (deriv (deriv G)) :=
    hGcompact.deriv.deriv
  obtain ⟨C, hC⟩ := hGderivDerivCompact.exists_bound_of_continuous
    hGderivDerivCont
  let C' : NNReal := ⟨max C (0 : ℝ), le_max_right _ _⟩
  have hC' : ∀ x : ℝ, ‖deriv (deriv G) x‖₊ ≤ C' := by
    intro x
    change ‖deriv (deriv G) x‖ ≤ max C (0 : ℝ)
    exact (hC x).trans (le_max_left _ _)
  have hGderivLipschitz : LipschitzWith C' (deriv G) :=
    lipschitzWith_of_nnnorm_deriv_le hGderivDiff hC'
  have hGderivCompact : HasCompactSupport (deriv G) := hGcompact.deriv
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    hGderivCompact.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℝ)
  let R : ℝ := R₀ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  have hGderiv_zero_left : ∀ x : ℝ, x ∈ Iic (-R) → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change x ≤ -R at hx
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith [hR₀pos]
  have hGderiv_zero_right : ∀ x : ℝ, x ∈ Ici R → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change R ≤ x at hx
      rw [abs_of_nonneg (by linarith)]
      exact hx
    linarith [hR₀pos]
  have hleft : eVariationOn (deriv G) (Iic (-R)) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_left x hx, hGderiv_zero_left y hy]
  have hright : eVariationOn (deriv G) (Ici R) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_right x hx, hGderiv_zero_right y hy]
  have hmid : BoundedVariationOn (deriv G) (Icc (-R) R) := by
    have hle : eVariationOn (deriv G) (Icc (-R) R) ≤
        C' * eVariationOn id (Icc (-R) R) := by
      exact hGderivLipschitz.lipschitzOnWith.comp_eVariationOn_le
        (mapsTo_id _)
    have hlt : eVariationOn (deriv G) (Icc (-R) R) < (⊤ : ENNReal) := by
      apply lt_of_le_of_lt hle
      rw [eVariationOn_id_Icc]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
    exact hlt.ne
  have hleft_mid_set : Iic (-R) ∪ Icc (-R) R = Iic R := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · change x ≤ -R at hx
        exact le_trans hx (by linarith [hRpos.le])
      · exact hx.2
    · intro hx
      by_cases h : x ≤ -R
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_ge h, hx⟩
  have hmid_right_set : Iic R ∪ Ici R = (Set.univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total x R
  have hleft_mid : eVariationOn (deriv G) (Iic R) =
      eVariationOn (deriv G) (Icc (-R) R) := by
    calc
      eVariationOn (deriv G) (Iic R) =
          eVariationOn (deriv G) (Iic (-R) ∪ Icc (-R) R) := by
            rw [hleft_mid_set]
      _ = eVariationOn (deriv G) (Iic (-R)) +
            edist (deriv G (-R)) (deriv G (-R)) +
              eVariationOn (deriv G) (Icc (-R) R) :=
        eVariationOn.union' (deriv G) (s := Iic (-R))
          (t := Icc (-R) R) (x := -R) (y := -R)
          ⟨by simp, fun x hx => hx⟩
          ⟨⟨by rfl, by linarith [hRpos.le]⟩, fun x hx => hx.1⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by simp [hleft]
  have htotal : BoundedVariationOn (deriv G) (Set.univ : Set ℝ) := by
    change eVariationOn (deriv G) (Set.univ : Set ℝ) ≠ (⊤ : ENNReal)
    calc
      eVariationOn (deriv G) (Set.univ : Set ℝ) =
          eVariationOn (deriv G) (Iic R ∪ Ici R) := by
            rw [hmid_right_set]
      _ = eVariationOn (deriv G) (Iic R) +
            edist (deriv G R) (deriv G R) +
              eVariationOn (deriv G) (Ici R) :=
        eVariationOn.union' (deriv G) (s := Iic R) (t := Ici R)
          (x := R) (y := R)
          ⟨by simp, fun x hx => hx⟩
          ⟨by simp, fun x hx => hx⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by
        simp [hright, hleft_mid]
      _ ≠ (⊤ : ENNReal) := hmid
  refine
    { even := hGeven
      continuous := hGdiff.continuous
      compactSupport := hGcompact
      piecewiseC2 := ?_
      valueAtZero := hG0
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro x hx
    exact hGdiff.contDiffAt.of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        apply WithTop.coe_le_coe.mpr
        exact le_top)
  · refine ⟨deriv G, deriv G, ?_, ?_, htotal, htotal⟩
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
  · exact chapter05_right_corner_origin_condition hG0 hGdiff.continuous
      ((hGdiff.differentiable (by simp) 0).hasDerivAt).hasDerivWithinAt

theorem chapter06_smooth_zero_summand_summable
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06SmoothCompactSupport F) :
    Summable (fun ρ : ℂ => chapter06ZeroSummand Z F ρ) := by
  classical
  rcases hF with ⟨hFeven, hFdiff, hFcompact⟩
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let B : ℝ → ℝ := b
  have hBdiff : ContDiff ℝ ∞ B := by
    simpa [B] using b.contDiff
  have hBcompact : HasCompactSupport B := by
    simpa [B] using b.hasCompactSupport
  have hBeven : Function.Even B := by
    intro x
    simpa [B] using b.neg x
  have hB0 : B 0 = 1 := by
    have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      simp [Metric.mem_closedBall, b]
    simpa [B] using b.one_of_mem_closedBall hzero
  have hB : Chapter06SmoothCompactSupport B := ⟨hBeven, hBdiff, hBcompact⟩
  have hBbasic : Chapter06BasicallyAdmissible B :=
    chapter06_smooth_compact_basic_of_value_at_zero_early hB hB0
  have htransform_integrable :
      ∀ {G : ℝ → ℝ}, Continuous G → HasCompactSupport G → ∀ s : ℂ,
        Integrable
          (fun x : ℝ => (G x : ℂ) * chapter05LaplaceKernel s x) := by
    intro G hGc hGcompact s
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp hGc).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    · exact (hGcompact.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hphi_smul :
      ∀ (a : ℝ) (G : ℝ → ℝ) (s : ℂ),
        chapter06Phi (fun x : ℝ => a * G x) s =
          (a : ℂ) * chapter06Phi G s := by
    intro a G s
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    simpa only [Complex.ofReal_mul, mul_assoc] using
      (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ))
        (a : ℂ)
        (fun x : ℝ => (G x : ℂ) * chapter05LaplaceKernel s x))
  have hphi_add :
      ∀ (G H : ℝ → ℝ), Continuous G → HasCompactSupport G →
        Continuous H → HasCompactSupport H → ∀ s : ℂ,
          chapter06Phi (fun x : ℝ => G x + H x) s =
            chapter06Phi G s + chapter06Phi H s := by
    intro G H hGc hGcompact hHc hHcompact s
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    simpa only [Complex.ofReal_add, add_mul] using
      (MeasureTheory.integral_add
        (htransform_integrable hGc hGcompact s)
        (htransform_integrable hHc hHcompact s))
  by_cases hF0 : F 0 ≠ 0
  · let G : ℝ → ℝ := fun x => F x / F 0
    have hGeven : Function.Even G := by
      intro x
      dsimp [G]
      rw [hFeven x]
    have hGdiff : ContDiff ℝ ∞ G := by
      simpa [G] using hFdiff.div_const (F 0)
    have hGcompact : HasCompactSupport G := by
      have hEq : G = F * (fun _ : ℝ => (F 0)⁻¹) := by
        funext x
        simp [G, div_eq_mul_inv]
      rw [hEq]
      exact hFcompact.mul_right (f' := fun _ : ℝ => (F 0)⁻¹)
    have hG : Chapter06SmoothCompactSupport G := ⟨hGeven, hGdiff, hGcompact⟩
    have hG0 : G 0 = 1 := by
      simp [G, hF0]
    have hGbasic : Chapter06BasicallyAdmissible G :=
      chapter06_smooth_compact_basic_of_value_at_zero_early hG hG0
    have hFG : F = fun x : ℝ => F 0 * G x := by
      funext x
      dsimp [G]
      field_simp [hF0]
    refine (chapter06_basic_zero_summand_summable K Z hGbasic).mul_left
      (F 0 : ℂ) |>.congr ?_
    intro ρ
    rw [hFG]
    simp only [chapter06ZeroSummand]
    rw [hphi_smul]
    simp [hG0]
    ring
  · let G : ℝ → ℝ := fun x => F x + B x
    have hF0' : F 0 = 0 := by
      exact not_ne_iff.mp hF0
    have hGeven : Function.Even G := by
      intro x
      dsimp [G]
      rw [hFeven x, hBeven x]
    have hGdiff : ContDiff ℝ ∞ G := by
      simpa [G] using hFdiff.add hBdiff
    have hGcompact : HasCompactSupport G := by
      have hEq : G = F + B := by
        funext x
        rfl
      rw [hEq]
      exact hFcompact.add hBcompact
    have hG : Chapter06SmoothCompactSupport G := ⟨hGeven, hGdiff, hGcompact⟩
    have hG0 : G 0 = 1 := by
      simp [G, hF0', hB0]
    have hGbasic : Chapter06BasicallyAdmissible G :=
      chapter06_smooth_compact_basic_of_value_at_zero_early hG hG0
    refine (chapter06_basic_zero_summand_summable K Z hGbasic).sub
        (chapter06_basic_zero_summand_summable K Z hBbasic) |>.congr ?_
    intro ρ
    dsimp [G]
    simp only [chapter06ZeroSummand]
    rw [hphi_add F B hFdiff.continuous hFcompact hBdiff.continuous hBcompact ρ]
    ring

theorem chapter06_zero_partial_sum_tendsto
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  classical
  let f : ℂ → ℂ := fun ρ => chapter06ZeroSummand Z F ρ
  have hf : Summable f := by
    simpa only [f] using chapter06_basic_zero_summand_summable K Z hF
  have hsum : HasSum f (∑' ρ : ℂ, f ρ) := hf.hasSum
  have hlim : Tendsto
      (fun T : ℝ => (chapter06ZeroWindowFinset Z T).sum f) atTop
      (𝓝 (∑' ρ : ℂ, f ρ)) := by
    intro U hU
    change ∀ᶠ T : ℝ in atTop,
      (chapter06ZeroWindowFinset Z T).sum f ∈ U
    have hU' : {s : Finset ℂ | s.sum f ∈ U} ∈
        (atTop : Filter (Finset ℂ)) := hsum hU
    rcases mem_atTop_sets.mp hU' with ⟨s, hs⟩
    have hband : ∀ᶠ T : ℝ in atTop,
        0 ≤ T ∧ ∀ ρ ∈ s, |ρ.im| + 1 ≤ T := by
      refine (eventually_ge_atTop (0 : ℝ)).and ?_
      rw [eventually_all_finset]
      intro ρ hρ
      exact eventually_ge_atTop _
    filter_upwards [hband] with T hT'
    have hsum_eq :
        ((chapter06ZeroWindowFinset Z T) ∪ s).sum f =
          (chapter06ZeroWindowFinset Z T).sum f := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro ρ hρ hρnot
      have hρs : ρ ∈ s := by
        rcases Finset.mem_union.mp hρ with hρwindow | hρs
        · exact False.elim (hρnot hρwindow)
        · exact hρs
      have hρzero : Z.multiplicity ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        have hρsupport : ρ ∈ Z.support :=
          (Z.support_iff_multiplicity_ne_zero ρ).mpr (Nat.ne_of_gt hmpos)
        apply hρnot
        apply (Z.locally_finite T).mem_toFinset.mpr
        exact ⟨hρsupport, by linarith [hT'.2 ρ hρs]⟩
      simp [chapter06ZeroSummand, hρzero]
    have hmem : (chapter06ZeroWindowFinset Z T) ∪ s ∈
        {u : Finset ℂ | u.sum f ∈ U} := by
      apply hs
      exact Finset.subset_union_right
    simpa [hsum_eq] using hmem
  change Tendsto
      (fun n => (chapter06ZeroWindowFinset Z (T n)).sum f) atTop
      (𝓝 (∑' ρ : ℂ, f ρ))
  exact hlim.comp hT

theorem chapter06_basic_zero_sum_is_symmetric_limit
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  exact chapter06_zero_partial_sum_tendsto K Z hF hT

theorem chapter06_symmetric_zero_value_independent_of_heights
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    {T U : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hU : Tendsto U atTop atTop) :
    Tendsto (fun n => chapter06ZeroPartialSum Z F (T n) -
      chapter06ZeroPartialSum Z F (U n)) atTop (𝓝 0) := by
  have hT' := chapter06_zero_partial_sum_tendsto K Z hF hT
  have hU' := chapter06_zero_partial_sum_tendsto K Z hF hU
  have hsub := hT'.sub hU'
  simpa using hsub

/-
SOURCE_NOTE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§6.5):
the source gives the standard convolution-and-normalization construction
informally.  The minimal usable interface is
`chapter06ApproximateIdentity` together with the explicit smoothed functions
and origin-correction factor below.
-/
theorem chapter06_approximate_identity_exists :
    ∃ η : ℕ → ℝ → ℝ, chapter06ApproximateIdentity η := by
  let c : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    { rIn := 1 / ((n + 1 : ℕ) : ℝ)
      rOut := 2 / ((n + 1 : ℕ) : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
        field_simp
        norm_num }
  let η : ℕ → ℝ → ℝ := fun n => (c n).normed volume
  have hc_out : ∀ n, (c n).rOut ≤ 2 := by
    intro n
    dsimp [c]
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    apply (div_le_iff₀ (by positivity : 0 < ((n + 1 : ℕ) : ℝ))).2
    nlinarith
  have hc_out_tendsto : Tendsto (fun n => (c n).rOut) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_natCast_atTop_atTop 2
    have hshift := hdiv.comp (tendsto_add_atTop_nat 1)
    simpa [c, Function.comp_def, Nat.cast_add, Nat.cast_one] using hshift
  have hη_integrable : ∀ n, Integrable (η n) := by
    intro n
    simpa [η] using (c n).integrable_normed
  have hη_compact : ∀ n, HasCompactSupport (η n) := by
    intro n
    simpa [η] using (c n).hasCompactSupport_normed
  have hη_support : ∃ R : ℝ, 0 ≤ R ∧ ∀ n,
      Function.support (η n) ⊆ Icc (-R) R := by
    refine ⟨2, by norm_num, ?_⟩
    intro n
    rw [(c n).support_normed_eq]
    intro x hx
    have hxabs : |x| < (c n).rOut := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hxabs' : -(c n).rOut < x ∧ x < (c n).rOut := abs_lt.mp hxabs
    have hxlt : x < 2 := lt_of_lt_of_le hxabs'.2 (hc_out n)
    have hxgt : -2 < x := (neg_le_neg (hc_out n)).trans_lt hxabs'.1
    exact ⟨hxgt.le, hxlt.le⟩
  have hη_contdiff : ∀ n, ContDiff ℝ ∞ (η n) := by
    intro n
    simpa [η] using (c n).contDiff_normed
  have hη_nonneg : ∀ n x, 0 ≤ η n x := by
    intro n x
    simpa [η] using (c n).nonneg_normed x
  have hη_even : ∀ n x, η n (-x) = η n x := by
    intro n x
    simpa [η] using (c n).normed_neg x
  have hη_integral : ∀ n, ∫ x : ℝ, η n x = 1 := by
    intro n
    simpa [η] using (c n).integral_normed
  have hη_converges : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)) := by
    intro φ hφ hφcompact
    have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := c) (g := φ) (μ := (volume : Measure ℝ)) (l := atTop)
        hc_out_tendsto hφ 0
    apply hconv.congr'
    filter_upwards [] with n
    simp [MeasureTheory.convolution_eq_swap, η]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [(c n).normed_neg x]
  exact ⟨η, ⟨hη_integrable, hη_compact, hη_support, hη_contdiff,
    hη_nonneg, hη_even, hη_integral, hη_converges⟩⟩

theorem chapter06_origin_correction_factor_apply_zero
    (η : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (n : ℕ)
    (h : chapter06SmoothedConvolution η F n 0 ≠ 0) :
    chapter06SmoothedTestFunction η F n 0 = 1 := by
  simp [chapter06SmoothedTestFunction, chapter06OriginCorrectionFactor, h]

theorem chapter06_smoothed_origin_eventually_nonzero
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop,
      chapter06SmoothedConvolution η F n 0 ≠ 0 := by
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hconv : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 (F 0)) :=
    hηconv F hF.continuous hF.compactSupport
  have hconv' : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 1) := by
    simpa [hF.valueAtZero] using hconv
  have heq : ∀ n, chapter06SmoothedConvolution η F n 0 =
      ∫ x : ℝ, η n x * F x := by
    intro n
    simp [chapter06SmoothedConvolution, chapter05Convolution,
      MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hF.even x]
  have hsmoothed : Tendsto
      (fun n => chapter06SmoothedConvolution η F n 0) atTop (𝓝 1) := by
    simpa only [heq] using hconv'
  filter_upwards [hsmoothed.eventually
      (Ioi_mem_nhds (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num))] with n hn
  exact ne_of_gt hn

theorem chapter06_origin_correction_factor_tendsto_one
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) := by
  have hne := chapter06_smoothed_origin_eventually_nonzero hη hF
  have hconv : Tendsto
      (fun n => chapter06SmoothedConvolution η F n 0) atTop (𝓝 1) := by
    rcases hη with ⟨_, _, _, _, _, _, _, hηconv⟩
    have hconv' := hηconv F hF.continuous hF.compactSupport
    have hconv'' : Tendsto (fun n => ∫ x : ℝ, η n x * F x) atTop (𝓝 1) := by
      simpa [hF.valueAtZero] using hconv'
    have heq : ∀ n, chapter06SmoothedConvolution η F n 0 =
        ∫ x : ℝ, η n x * F x := by
      intro n
      simp [chapter06SmoothedConvolution, chapter05Convolution,
        MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hF.even x]
    simpa only [heq] using hconv''
  have hinv : Tendsto
      (fun n => (chapter06SmoothedConvolution η F n 0)⁻¹) atTop (𝓝 1) := by
    simpa using hconv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  filter_upwards [hne] with n hn
  simp [chapter06OriginCorrectionFactor, hn]

private theorem chapter06_smooth_compact_basic_of_value_at_zero
    {G : ℝ → ℝ} (hG : Chapter06SmoothCompactSupport G) (hG0 : G 0 = 1) :
    Chapter06BasicallyAdmissible G := by
  rcases hG with ⟨hGeven, hGdiff, hGcompact⟩
  have hGderivDiff : Differentiable ℝ (deriv G) := by
    exact (contDiff_infty_iff_deriv.mp hGdiff).2.differentiable (by simp)
  have hGderivDerivCont : Continuous (deriv (deriv G)) := by
    have hGderivDeriv : ContDiff ℝ ∞ (deriv (deriv G)) := by
      exact (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp hGdiff).2).2
    exact hGderivDeriv.continuous
  have hGderivDerivCompact : HasCompactSupport (deriv (deriv G)) :=
    hGcompact.deriv.deriv
  obtain ⟨C, hC⟩ := hGderivDerivCompact.exists_bound_of_continuous
    hGderivDerivCont
  let C' : NNReal := ⟨max C (0 : ℝ), le_max_right _ _⟩
  have hC' : ∀ x : ℝ, ‖deriv (deriv G) x‖₊ ≤ C' := by
    intro x
    change ‖deriv (deriv G) x‖ ≤ max C (0 : ℝ)
    exact (hC x).trans (le_max_left _ _)
  have hGderivLipschitz : LipschitzWith C' (deriv G) :=
    lipschitzWith_of_nnnorm_deriv_le hGderivDiff hC'
  have hGderivCompact : HasCompactSupport (deriv G) := hGcompact.deriv
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    hGderivCompact.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℝ)
  let R : ℝ := R₀ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  have hGderiv_zero_left : ∀ x : ℝ, x ∈ Iic (-R) → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change x ≤ -R at hx
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith [hR₀pos]
  have hGderiv_zero_right : ∀ x : ℝ, x ∈ Ici R → deriv G x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    have hxball := hR₀ hxt
    have hxabs : |x| ≤ R₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    have hxabs' : R ≤ |x| := by
      change R ≤ x at hx
      rw [abs_of_nonneg (by linarith)]
      exact hx
    linarith [hR₀pos]
  have hleft : eVariationOn (deriv G) (Iic (-R)) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_left x hx, hGderiv_zero_left y hy]
  have hright : eVariationOn (deriv G) (Ici R) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hGderiv_zero_right x hx, hGderiv_zero_right y hy]
  have hmid : BoundedVariationOn (deriv G) (Icc (-R) R) := by
    have hle : eVariationOn (deriv G) (Icc (-R) R) ≤
        C' * eVariationOn id (Icc (-R) R) := by
      exact hGderivLipschitz.lipschitzOnWith.comp_eVariationOn_le
        (mapsTo_id _) 
    have hlt : eVariationOn (deriv G) (Icc (-R) R) < (⊤ : ENNReal) := by
      apply lt_of_le_of_lt hle
      rw [eVariationOn_id_Icc]
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
    exact hlt.ne
  have hleft_mid_set : Iic (-R) ∪ Icc (-R) R = Iic R := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · change x ≤ -R at hx
        exact le_trans hx (by linarith [hRpos.le])
      · exact hx.2
    · intro hx
      by_cases h : x ≤ -R
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_ge h, hx⟩
  have hmid_right_set : Iic R ∪ Ici R = (Set.univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      exact le_total x R
  have hleft_mid : eVariationOn (deriv G) (Iic R) =
      eVariationOn (deriv G) (Icc (-R) R) := by
    calc
      eVariationOn (deriv G) (Iic R) =
          eVariationOn (deriv G) (Iic (-R) ∪ Icc (-R) R) := by
            rw [hleft_mid_set]
      _ =
          eVariationOn (deriv G) (Iic (-R)) +
            edist (deriv G (-R)) (deriv G (-R)) +
              eVariationOn (deriv G) (Icc (-R) R) :=
        eVariationOn.union' (deriv G) (s := Iic (-R))
          (t := Icc (-R) R) (x := -R) (y := -R)
          ⟨by simp, fun x hx => hx⟩
          ⟨⟨by rfl, by linarith [hRpos.le]⟩, fun x hx => hx.1⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by simp [hleft]
  have htotal : BoundedVariationOn (deriv G) (Set.univ : Set ℝ) := by
    change eVariationOn (deriv G) (Set.univ : Set ℝ) ≠ (⊤ : ENNReal)
    calc
      eVariationOn (deriv G) (Set.univ : Set ℝ) =
          eVariationOn (deriv G) (Iic R ∪ Ici R) := by
            rw [hmid_right_set]
      _ =
          eVariationOn (deriv G) (Iic R) +
            edist (deriv G R) (deriv G R) +
              eVariationOn (deriv G) (Ici R) :=
        eVariationOn.union' (deriv G) (s := Iic R) (t := Ici R)
          (x := R) (y := R)
          ⟨by simp, fun x hx => hx⟩
          ⟨by simp, fun x hx => hx⟩ le_rfl
      _ = eVariationOn (deriv G) (Icc (-R) R) := by
        simp [hright, hleft_mid]
      _ ≠ (⊤ : ENNReal) := hmid
  refine
    { even := hGeven
      continuous := hGdiff.continuous
      compactSupport := hGcompact
      piecewiseC2 := ?_
      valueAtZero := hG0
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro x hx
    exact hGdiff.contDiffAt.of_le
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        apply WithTop.coe_le_coe.mpr
        exact le_top)
  · refine ⟨deriv G, deriv G, ?_, ?_, htotal, htotal⟩
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
    · intro x
      exact ((hGdiff.differentiable (by simp) x).hasDerivAt).hasDerivWithinAt
  · exact chapter05_right_corner_origin_condition hG0 hGdiff.continuous
      ((hGdiff.differentiable (by simp) 0).hasDerivAt).hasDerivWithinAt

private theorem chapter06_smoothed_test_function_smooth_compact
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) (n : ℕ) :
    Chapter06SmoothCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hconv_smooth : ContDiff ℝ ∞
      (chapter06SmoothedConvolution η F n) := by
    unfold chapter06SmoothedConvolution chapter05Convolution
    have hflip :
        MeasureTheory.convolution (η n) F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume =
          MeasureTheory.convolution F (η n)
            (ContinuousLinearMap.lsmul ℝ ℝ).flip volume := by
      simpa only [ContinuousLinearMap.flip_flip] using
        (MeasureTheory.convolution_flip
          (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
          (f := F) (g := η n) (μ := (volume : Measure ℝ)))
    rw [hflip]
    exact (hηcompact n).contDiff_convolution_right
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip)
      hF.continuous.locallyIntegrable (hηdiff n)
  have hconv_compact : HasCompactSupport
      (chapter06SmoothedConvolution η F n) := by
    unfold chapter06SmoothedConvolution chapter05Convolution
    exact (hηcompact n).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hF.compactSupport
  have hconv_even : Function.Even
      (chapter06SmoothedConvolution η F n) := by
    intro x
    unfold chapter06SmoothedConvolution chapter05Convolution
    exact MeasureTheory.convolution_neg_of_neg_eq
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (Eventually.of_forall (hηeven n))
      (Eventually.of_forall hF.even)
  have htest_diff : ContDiff ℝ ∞
      (chapter06SmoothedTestFunction η F n) := by
    have hscalar : ContDiff ℝ ∞ (fun _ : ℝ =>
        chapter06OriginCorrectionFactor η F n) := contDiff_const
    change ContDiff ℝ ∞ (fun x : ℝ =>
      chapter06OriginCorrectionFactor η F n *
        chapter06SmoothedConvolution η F n x)
    exact hscalar.mul hconv_smooth
  have htest_compact : HasCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
    change HasCompactSupport
      ((fun _ : ℝ => chapter06OriginCorrectionFactor η F n) *
        chapter06SmoothedConvolution η F n)
    exact hconv_compact.mul_left
  have htest_even : Function.Even
      (chapter06SmoothedTestFunction η F n) := by
    intro x
    simp [chapter06SmoothedTestFunction, hconv_even x]
  exact ⟨htest_even, htest_diff, htest_compact⟩

theorem chapter06_smoothed_test_functions_basic_admissible
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ᶠ n : ℕ in atTop, Chapter06BasicallyAdmissible
      (chapter06SmoothedTestFunction η F n) := by
  filter_upwards [chapter06_smoothed_origin_eventually_nonzero hη hF] with n hn
  apply chapter06_smooth_compact_basic_of_value_at_zero
  · exact chapter06_smoothed_test_function_smooth_compact hη hF n
  · exact chapter06_origin_correction_factor_apply_zero η F n hn

theorem chapter06_smoothed_test_functions_smooth_compact
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ n, Chapter06SmoothCompactSupport
      (chapter06SmoothedTestFunction η F n) := by
  intro n
  exact chapter06_smoothed_test_function_smooth_compact hη hF n

theorem chapter06_smoothed_test_functions_decay_uniformly
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ σ t : ℝ,
      |σ| ≤ R →
      ‖chapter06Phi (chapter06SmoothedTestFunction η F n)
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2 := by
  classical
  have hcorr : Tendsto
      (fun n : ℕ => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) :=
    chapter06_origin_correction_factor_tendsto_one (η := η) (F := F) hη hF
  have hrange := Metric.isBounded_range_of_tendsto
    (fun n : ℕ => chapter06OriginCorrectionFactor η F n) hcorr
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hrange
  have hcorr_bound : ∀ n : ℕ,
      ‖chapter06OriginCorrectionFactor η F n‖ ≤ M := by
    intro n
    have hn := hM (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hn
  have hMnonneg : 0 ≤ M := by
    exact (norm_nonneg _).trans (hcorr_bound 0)
  intro R hR
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  obtain ⟨Rη, hRη, hηsupport⟩ := hηsupport
  let E : ℝ := Real.exp ((R + 1 / 2) * Rη)
  have hkernel_bound (σ t y : ℝ) (hσ : |σ| ≤ R)
      (hy : y ∈ Icc (-Rη) Rη) :
      ‖chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤ E := by
    rw [chapter05LaplaceKernel, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hσ' : -R ≤ σ ∧ σ ≤ R := abs_le.mp hσ
    have hσabs : |σ - 1 / 2| ≤ R + 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hσ'.1, hσ'.2]
    have hyabs : |y| ≤ Rη := by
      rw [abs_le]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc
      (((σ : ℂ) + (t : ℂ) * Complex.I - (1 / 2 : ℂ)) * (y : ℂ)).re =
          (σ - 1 / 2) * y := by norm_num [Complex.mul_re]
      _ ≤ |σ - 1 / 2| * |y| := by
        exact le_trans (le_abs_self _) (by rw [abs_mul])
      _ ≤ (R + 1 / 2) * Rη := by
        exact mul_le_mul hσabs hyabs (abs_nonneg _)
          (by linarith [hσ'.1, hσ'.2])
      _ = ((R + 1 / 2) * Rη) := rfl
  have hηweighted (n : ℕ) (s : ℂ) :
      Integrable (fun y : ℝ =>
        (η n y : ℂ) * chapter05LaplaceKernel s y) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp (hηdiff n).continuous).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    · exact ((hηcompact n).comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hFweighted (s : ℂ) : Integrable (fun y : ℝ =>
      (F y : ℂ) * chapter05LaplaceKernel s y) volume :=
    chapter05_basically_admissible_laplace_integrable hF s
  obtain ⟨Cdec, hCdec, hdecay⟩ :=
    chapter05_basically_admissible_vertical_decay hF R hR
  have hηtransform_bound (n : ℕ) (σ t : ℝ) (hσ : |σ| ≤ R) :
      ‖∫ y : ℝ, (η n y : ℂ) *
          chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤ E := by
    calc
      ‖∫ y : ℝ, (η n y : ℂ) *
          chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤
          ∫ y : ℝ, E * η n y := by
            refine norm_integral_le_of_norm_le
              ((hηint n).const_mul E) ?_
            filter_upwards [] with y
            by_cases hy : η n y = 0
            · simp [hy]
            · have hy' := hηsupport n hy
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hηnonneg n y)]
              simpa [mul_comm] using
                (mul_le_mul_of_nonneg_left
                  (hkernel_bound σ t y hσ (hy' : y ∈ Icc (-Rη) Rη))
                  (hηnonneg n y))
      _ = E := by
        rw [integral_const_mul, hηnorm n]
        simp
  have hconv_weighted (n : ℕ) (s : ℂ) (x : ℝ) :
      ((chapter06SmoothedConvolution η F n x : ℝ) : ℂ) *
          chapter05LaplaceKernel s x =
        MeasureTheory.convolution
          (fun y : ℝ => (η n y : ℂ) * chapter05LaplaceKernel s y)
          (fun y : ℝ => (F y : ℂ) * chapter05LaplaceKernel s y)
          (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
    let I : ℝ := ∫ y : ℝ, η n y * F (x - y)
    have hcast :
        (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) =
          (I : ℂ) := by
      calc
        (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) =
            ∫ y : ℝ, ((η n y * F (x - y) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [Complex.ofReal_mul]
        _ = (I : ℂ) := by
          dsimp [I]
          exact integral_ofReal (𝕜 := ℂ)
    unfold chapter06SmoothedConvolution chapter05Convolution
    simp only [MeasureTheory.convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    change (I : ℂ) * chapter05LaplaceKernel s x = _
    rw [← hcast]
    calc
      (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) *
          chapter05LaplaceKernel s x =
        chapter05LaplaceKernel s x *
          (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) := by
            rw [mul_comm]
      _ = ∫ y : ℝ, chapter05LaplaceKernel s x *
          ((η n y : ℂ) * (F (x - y) : ℂ)) := by
            rw [← integral_const_mul]
      _ = ∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y *
          ((F (x - y) : ℂ) * chapter05LaplaceKernel s (x - y)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [chapter05LaplaceKernel]
        have hexp :
            Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) =
              Complex.exp ((s - (1 / 2 : ℂ)) * (y : ℂ)) *
                Complex.exp ((s - (1 / 2 : ℂ)) * ((x - y : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hexp]
        ring
  have hphi_conv (n : ℕ) (s : ℂ) :
      chapter06Phi (chapter06SmoothedConvolution η F n) s =
        (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
          chapter06Phi F s := by
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    have hleft :
        (∫ x : ℝ, (chapter06SmoothedConvolution η F n x : ℂ) *
            chapter05LaplaceKernel s x) =
          ∫ x : ℝ, MeasureTheory.convolution
            (fun y : ℝ => (η n y : ℂ) * chapter05LaplaceKernel s y)
            (fun y : ℝ => (F y : ℂ) * chapter05LaplaceKernel s y)
            (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hconv_weighted n s x
    rw [hleft]
    rw [MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.lsmul ℂ ℂ)
      (hηweighted n s) (hFweighted s)]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hphi_smul (a : ℝ) (G : ℝ → ℝ) (s : ℂ) :
      chapter06Phi (fun x : ℝ => a * G x) s =
        (a : ℂ) * chapter06Phi G s := by
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Complex.ofReal_mul, mul_assoc]
  have hphi_smoothed (n : ℕ) (s : ℂ) :
      chapter06Phi (chapter06SmoothedTestFunction η F n) s =
        (chapter06OriginCorrectionFactor η F n : ℂ) *
          (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
            chapter06Phi F s := by
    calc
      chapter06Phi (chapter06SmoothedTestFunction η F n) s =
          (chapter06OriginCorrectionFactor η F n : ℂ) *
            chapter06Phi (chapter06SmoothedConvolution η F n) s := by
        change chapter06Phi (fun x : ℝ =>
          chapter06OriginCorrectionFactor η F n *
            chapter06SmoothedConvolution η F n x) s = _
        exact hphi_smul (chapter06OriginCorrectionFactor η F n)
          (chapter06SmoothedConvolution η F n) s
      _ = (chapter06OriginCorrectionFactor η F n : ℂ) *
          ((∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
            chapter06Phi F s) := by rw [hphi_conv]
      _ = (chapter06OriginCorrectionFactor η F n : ℂ) *
          (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
            chapter06Phi F s := by ring
  refine ⟨M * E * Cdec, by positivity, ?_⟩
  intro n σ t hσ
  rw [hphi_smoothed]
  calc
    ‖(chapter06OriginCorrectionFactor η F n : ℂ) *
        (∫ y : ℝ, (η n y : ℂ) *
          chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y) *
          chapter06Phi F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖chapter06OriginCorrectionFactor η F n‖ *
          ‖∫ y : ℝ, (η n y : ℂ) *
            chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ *
          ‖chapter06Phi F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
            simp
    _ ≤ M * E * (Cdec / (1 + |t|) ^ 2) := by
      gcongr
      · exact hcorr_bound n
      · exact hηtransform_bound n σ t hσ
      · exact hdecay σ t hσ
    _ = (M * E * Cdec) / (1 + |t|) ^ 2 := by ring

private theorem chapter06_smoothed_phi_factorization
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    ∀ n : ℕ, ∀ s : ℂ,
      chapter06Phi (chapter06SmoothedTestFunction η F n) s =
        (chapter06OriginCorrectionFactor η F n : ℂ) *
          (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
            chapter06Phi F s := by
  classical
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hηweighted (n : ℕ) (s : ℂ) :
      Integrable (fun y : ℝ =>
        (η n y : ℂ) * chapter05LaplaceKernel s y) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp (hηdiff n).continuous).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    · exact ((hηcompact n).comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hFweighted (s : ℂ) : Integrable (fun y : ℝ =>
      (F y : ℂ) * chapter05LaplaceKernel s y) volume :=
    chapter05_basically_admissible_laplace_integrable hF s
  have hconv_weighted (n : ℕ) (s : ℂ) (x : ℝ) :
      ((chapter06SmoothedConvolution η F n x : ℝ) : ℂ) *
          chapter05LaplaceKernel s x =
        MeasureTheory.convolution
          (fun y : ℝ => (η n y : ℂ) * chapter05LaplaceKernel s y)
          (fun y : ℝ => (F y : ℂ) * chapter05LaplaceKernel s y)
          (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
    let I : ℝ := ∫ y : ℝ, η n y * F (x - y)
    have hcast :
        (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) =
          (I : ℂ) := by
      calc
        (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) =
            ∫ y : ℝ, ((η n y * F (x - y) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [Complex.ofReal_mul]
        _ = (I : ℂ) := by
          dsimp [I]
          exact integral_ofReal (𝕜 := ℂ)
    unfold chapter06SmoothedConvolution chapter05Convolution
    simp only [MeasureTheory.convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    change (I : ℂ) * chapter05LaplaceKernel s x = _
    rw [← hcast]
    calc
      (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) *
          chapter05LaplaceKernel s x =
        chapter05LaplaceKernel s x *
          (∫ y : ℝ, (η n y : ℂ) * (F (x - y) : ℂ)) := by
            rw [mul_comm]
      _ = ∫ y : ℝ, chapter05LaplaceKernel s x *
          ((η n y : ℂ) * (F (x - y) : ℂ)) := by
            rw [← integral_const_mul]
      _ = ∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y *
          ((F (x - y) : ℂ) * chapter05LaplaceKernel s (x - y)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [chapter05LaplaceKernel]
        have hexp :
            Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ)) =
              Complex.exp ((s - (1 / 2 : ℂ)) * (y : ℂ)) *
                Complex.exp ((s - (1 / 2 : ℂ)) * ((x - y : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hexp]
        ring
  have hphi_conv (n : ℕ) (s : ℂ) :
      chapter06Phi (chapter06SmoothedConvolution η F n) s =
        (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
          chapter06Phi F s := by
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    have hleft :
        (∫ x : ℝ, (chapter06SmoothedConvolution η F n x : ℂ) *
            chapter05LaplaceKernel s x) =
          ∫ x : ℝ, MeasureTheory.convolution
            (fun y : ℝ => (η n y : ℂ) * chapter05LaplaceKernel s y)
            (fun y : ℝ => (F y : ℂ) * chapter05LaplaceKernel s y)
            (ContinuousLinearMap.lsmul ℂ ℂ) volume x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hconv_weighted n s x
    rw [hleft]
    rw [MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.lsmul ℂ ℂ)
      (hηweighted n s) (hFweighted s)]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hphi_smul (a : ℝ) (G : ℝ → ℝ) (s : ℂ) :
      chapter06Phi (fun x : ℝ => a * G x) s =
        (a : ℂ) * chapter06Phi G s := by
    unfold chapter06Phi chapter05BilateralLaplaceTransform
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp [Complex.ofReal_mul, mul_assoc]
  intro n s
  calc
    chapter06Phi (chapter06SmoothedTestFunction η F n) s =
        (chapter06OriginCorrectionFactor η F n : ℂ) *
          chapter06Phi (chapter06SmoothedConvolution η F n) s := by
      change chapter06Phi (fun x : ℝ =>
        chapter06OriginCorrectionFactor η F n *
          chapter06SmoothedConvolution η F n x) s = _
      exact hphi_smul (chapter06OriginCorrectionFactor η F n)
        (chapter06SmoothedConvolution η F n) s
    _ = (chapter06OriginCorrectionFactor η F n : ℂ) *
        ((∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
          chapter06Phi F s) := by rw [hphi_conv]
    _ = (chapter06OriginCorrectionFactor η F n : ℂ) *
        (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) *
          chapter06Phi F s := by ring

private theorem chapter06_approximate_identity_laplace_tendsto_one
    {η : ℕ → ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η) (s : ℂ) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y) atTop (𝓝 1) := by
  classical
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  obtain ⟨Rη, hRη, hηsupport⟩ := hηsupport
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := Rη + 1
      rOut := Rη + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let B : ℝ → ℝ := b
  have hBdiff : ContDiff ℝ ∞ B := by
    simpa [B] using b.contDiff
  have hBcompact : HasCompactSupport B := by
    simpa [B] using b.hasCompactSupport
  have hBone : ∀ y : ℝ, y ∈ Icc (-Rη) Rη → B y = 1 := by
    intro y hy
    have hyabs : |y| ≤ Rη := by
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hyball : y ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      simpa [Metric.mem_closedBall, Real.dist_eq, b] using
        (show |y| ≤ Rη + 1 by linarith)
    simpa [B] using b.one_of_mem_closedBall hyball
  have hB0 : B 0 = 1 := by
    have hzero : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      simp [Metric.mem_closedBall, b]
      linarith [hRη]
    simpa [B] using b.one_of_mem_closedBall hzero
  have hKcont : Continuous (fun y : ℝ => chapter05LaplaceKernel s y) := by
    exact Complex.continuous_exp.comp
      ((continuous_const.sub continuous_const).mul
        (Complex.continuous_ofReal.comp continuous_id))
  let φre : ℝ → ℝ := fun y =>
    B y * (chapter05LaplaceKernel s y).re
  let φim : ℝ → ℝ := fun y =>
    B y * (chapter05LaplaceKernel s y).im
  have hφrecont : Continuous φre := by
    dsimp [φre]
    exact hBdiff.continuous.mul (Complex.continuous_re.comp hKcont)
  have hφimcont : Continuous φim := by
    dsimp [φim]
    exact hBdiff.continuous.mul (Complex.continuous_im.comp hKcont)
  have hφrecompact : HasCompactSupport φre := by
    dsimp [φre]
    exact hBcompact.mul_right
  have hφimcompact : HasCompactSupport φim := by
    dsimp [φim]
    exact hBcompact.mul_right
  have hφre0 : φre 0 = 1 := by
    dsimp [φre]
    rw [hB0]
    simp [chapter05LaplaceKernel]
  have hφim0 : φim 0 = 0 := by
    dsimp [φim]
    rw [hB0]
    simp [chapter05LaplaceKernel]
  have hlimre : Tendsto (fun n : ℕ =>
      ∫ y : ℝ, η n y * φre y) atTop (𝓝 1) := by
    simpa only [hφre0] using hηconv φre hφrecont hφrecompact
  have hlimim : Tendsto (fun n : ℕ =>
      ∫ y : ℝ, η n y * φim y) atTop (𝓝 0) := by
    simpa only [hφim0] using hηconv φim hφimcont hφimcompact
  have hηweighted (n : ℕ) :
      Integrable (fun y : ℝ =>
        (η n y : ℂ) * chapter05LaplaceKernel s y) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_ofReal.comp (hηdiff n).continuous).mul hKcont
    · exact ((hηcompact n).comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  let J : ℕ → ℂ := fun n =>
    ∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel s y
  have hreal_eq (n : ℕ) :
      (J n).re = ∫ y : ℝ, η n y * φre y := by
    calc
      (J n).re = ∫ y : ℝ,
          (((η n y : ℂ) * chapter05LaplaceKernel s y).re) := by
        dsimp [J]
        exact (integral_re (hηweighted n)).symm
      _ = ∫ y : ℝ, η n y * φre y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hyzero : η n y = 0
        · simp [hyzero, φre]
        · have hy := hηsupport n hyzero
          have hby := hBone y hy
          simp [φre, hby, Complex.mul_re]
  have himag_eq (n : ℕ) :
      (J n).im = ∫ y : ℝ, η n y * φim y := by
    calc
      (J n).im = ∫ y : ℝ,
          (((η n y : ℂ) * chapter05LaplaceKernel s y).im) := by
        dsimp [J]
        exact (integral_im (hηweighted n)).symm
      _ = ∫ y : ℝ, η n y * φim y := by
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hyzero : η n y = 0
        · simp [hyzero, φim]
        · have hy := hηsupport n hyzero
          have hby := hBone y hy
          simp [φim, hby, Complex.mul_im]
  have hreal : Tendsto (fun n : ℕ => (J n).re) atTop (𝓝 1) := by
    refine hlimre.congr' ?_
    filter_upwards [] with n
    exact (hreal_eq n).symm
  have himag : Tendsto (fun n : ℕ => (J n).im) atTop (𝓝 0) := by
    refine hlimim.congr' ?_
    filter_upwards [] with n
    exact (himag_eq n).symm
  change Tendsto J atTop (𝓝 (1 : ℂ))
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  refine squeeze_zero
    (f := fun n : ℕ => ‖J n - (1 : ℂ)‖)
    (g := fun n : ℕ => |(J n).re - 1| + |(J n).im|)
    (fun n => norm_nonneg _) ?_ ?_
  · intro n
    have hbound :=
      Complex.norm_le_abs_re_add_abs_im (J n - (1 : ℂ))
    simpa using hbound
  · have hreal_sub : Tendsto (fun n : ℕ => (J n).re - 1) atTop (𝓝 0) := by
      simpa using hreal.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    simpa using hreal_sub.abs.add himag.abs

theorem chapter06_smoothed_zero_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06SymmetricZeroSum Z
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06SymmetricZeroSum Z F)) := by
  classical
  have hηdata := hη
  rcases hηdata with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  obtain ⟨Rη, hRη, hηsupport⟩ := hηsupport
  let E : ℝ := Real.exp ((1 + 1 / 2) * Rη)
  have hkernel_bound (σ t y : ℝ) (hσ : |σ| ≤ 1)
      (hy : y ∈ Icc (-Rη) Rη) :
      ‖chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤ E := by
    rw [chapter05LaplaceKernel, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hσ' : -1 ≤ σ ∧ σ ≤ 1 := abs_le.mp hσ
    have hσabs : |σ - 1 / 2| ≤ 1 + 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hσ'.1, hσ'.2]
    have hyabs : |y| ≤ Rη := by
      rw [abs_le]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc
      (((σ : ℂ) + (t : ℂ) * Complex.I - (1 / 2 : ℂ)) * (y : ℂ)).re =
          (σ - 1 / 2) * y := by norm_num [Complex.mul_re]
      _ ≤ |σ - 1 / 2| * |y| := by
        exact le_trans (le_abs_self _) (by rw [abs_mul])
      _ ≤ (1 + 1 / 2) * Rη := by
        exact mul_le_mul hσabs hyabs (abs_nonneg _)
          (by positivity)
      _ = ((1 + 1 / 2) * Rη) := rfl
  have hηtransform_bound (n : ℕ) (σ t : ℝ) (hσ : |σ| ≤ 1) :
      ‖∫ y : ℝ, (η n y : ℂ) *
          chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤ E := by
    calc
      ‖∫ y : ℝ, (η n y : ℂ) *
          chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) y‖ ≤
          ∫ y : ℝ, E * η n y := by
            refine norm_integral_le_of_norm_le
              ((hηint n).const_mul E) ?_
            filter_upwards [] with y
            by_cases hy : η n y = 0
            · simp [hy]
            · have hy' := hηsupport n hy
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hηnonneg n y)]
              simpa [mul_comm] using
                (mul_le_mul_of_nonneg_left
                  (hkernel_bound σ t y hσ
                    (hy' : y ∈ Icc (-Rη) Rη))
                  (hηnonneg n y))
      _ = E := by
        rw [integral_const_mul, hηnorm n]
        simp
  have hcorr : Tendsto
      (fun n : ℕ => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) :=
    chapter06_origin_correction_factor_tendsto_one hη hF
  have hrange := Metric.isBounded_range_of_tendsto
    (fun n : ℕ => chapter06OriginCorrectionFactor η F n) hcorr
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hrange
  have hcorr_bound : ∀ n : ℕ,
      ‖chapter06OriginCorrectionFactor η F n‖ ≤ M := by
    intro n
    have hn := hM (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hn
  have hMnonneg : 0 ≤ M := by
    exact (norm_nonneg _).trans (hcorr_bound 0)
  have hcorr_complex : Tendsto
      (fun n : ℕ => (chapter06OriginCorrectionFactor η F n : ℂ)) atTop (𝓝 1) :=
    hcorr.ofReal
  have hpoint_bound (n : ℕ) (ρ : ℂ) :
      ‖chapter06ZeroSummand Z
          (chapter06SmoothedTestFunction η F n) ρ‖ ≤
        (M * E) * ‖chapter06ZeroSummand Z F ρ‖ := by
    by_cases hρ : ρ ∈ Z.support
    · have hstrip := Z.critical_strip hρ
      have hre : |ρ.re| ≤ (1 : ℝ) := by
        rw [abs_of_nonneg hstrip.1]
        exact hstrip.2
      have hrepr : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hηbound :
          ‖∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel ρ y‖ ≤ E := by
        rw [hrepr]
        exact hηtransform_bound n ρ.re ρ.im hre
      change ‖(Z.multiplicity ρ : ℂ) *
          chapter06Phi (chapter06SmoothedTestFunction η F n) ρ‖ ≤
        (M * E) * ‖(Z.multiplicity ρ : ℂ) * chapter06Phi F ρ‖
      rw [chapter06_smoothed_phi_factorization hη hF n ρ]
      calc
        ‖(Z.multiplicity ρ : ℂ) *
              ((chapter06OriginCorrectionFactor η F n : ℂ) *
                (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel ρ y) *
                  chapter06Phi F ρ)‖ =
            ‖(Z.multiplicity ρ : ℂ)‖ *
              ‖chapter06OriginCorrectionFactor η F n‖ *
                ‖∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel ρ y‖ *
                  ‖chapter06Phi F ρ‖ := by simp [mul_assoc]
        _ ≤ ‖(Z.multiplicity ρ : ℂ)‖ * M * E *
              ‖chapter06Phi F ρ‖ := by
          gcongr
          · simpa using hcorr_bound n
        _ = (M * E) * ‖(Z.multiplicity ρ : ℂ) *
              chapter06Phi F ρ‖ := by simp; ring
    · have hm : Z.multiplicity ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        apply hρ
        exact (Z.support_iff_multiplicity_ne_zero ρ).mpr (Nat.ne_of_gt hmpos)
      simp [chapter06ZeroSummand, hm]
  let f : ℕ → ℂ → ℂ := fun n ρ =>
    chapter06ZeroSummand Z (chapter06SmoothedTestFunction η F n) ρ
  let g : ℂ → ℂ := fun ρ => chapter06ZeroSummand Z F ρ
  let bound : ℂ → ℝ := fun ρ => (M * E) * ‖g ρ‖
  have h_sum : Summable bound := by
    dsimp [bound, g]
    have hbase_norm : Summable (fun ρ : ℂ =>
        ‖chapter06ZeroSummand Z F ρ‖) :=
      summable_norm_iff.mpr (chapter06_basic_zero_summand_summable K Z hF)
    exact hbase_norm.mul_left (M * E)
  have h_bound : ∀ᶠ n : ℕ in atTop, ∀ ρ : ℂ,
      ‖f n ρ‖ ≤ bound ρ := by
    filter_upwards [] with n ρ
    simpa [f, g, bound] using hpoint_bound n ρ
  have h_pointwise : ∀ ρ : ℂ,
      Tendsto (fun n : ℕ => f n ρ) atTop (𝓝 (g ρ)) := by
    intro ρ
    have heta := chapter06_approximate_identity_laplace_tendsto_one hη ρ
    have hfac : Tendsto (fun n : ℕ =>
        (chapter06OriginCorrectionFactor η F n : ℂ) *
          (∫ y : ℝ, (η n y : ℂ) * chapter05LaplaceKernel ρ y)) atTop
        (𝓝 1) := by
      simpa using hcorr_complex.mul heta
    have hphi : Tendsto (fun n : ℕ =>
        chapter06Phi (chapter06SmoothedTestFunction η F n) ρ) atTop
        (𝓝 (chapter06Phi F ρ)) := by
      have h := hfac.mul_const (chapter06Phi F ρ)
      simpa only [one_mul] using
        h.congr' (Eventually.of_forall (fun n =>
          (chapter06_smoothed_phi_factorization hη hF n ρ).symm))
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (Z.multiplicity ρ : ℂ)) atTop (𝓝 (Z.multiplicity ρ : ℂ))).mul hphi
    simpa [f, g, chapter06ZeroSummand] using hmul
  have hsum := tendsto_tsum_of_dominated_convergence h_sum h_pointwise h_bound
  simpa [f, g, chapter06SymmetricZeroSum] using hsum

theorem chapter06_smoothed_prime_sum_dominated_convergence
    (K : Type*) [Field K] [NumberField K]
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06PrimeContribution K
      (chapter06SmoothedTestFunction η F n)) atTop
      (𝓝 (chapter06PrimeContribution K F)) := by
  classical
  let G : ℕ → ℝ → ℝ :=
    fun n => chapter06SmoothedTestFunction η F n
  have hcorr : Tendsto
      (fun n => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) :=
    chapter06_origin_correction_factor_tendsto_one hη hF
  rcases hη with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  obtain ⟨RF₀, hRF⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      hF.compactSupport.isBounded
  let RF : ℝ := max RF₀ 0
  have hRF_nonneg : 0 ≤ RF := by
    dsimp [RF]
    exact le_max_right _ _
  have hFsupport : Function.support F ⊆ Icc (-RF) RF := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) RF₀ :=
      hRF (subset_closure hx)
    have habs : |x| ≤ RF₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx'
    have habs' : |x| ≤ RF := habs.trans (le_max_left _ _)
    exact abs_le.mp habs'
  rcases hηsupport with ⟨Rη, hRη, hηsupport⟩
  let T : ℝ := Rη + RF
  have hT : 0 ≤ T := by
    dsimp [T]
    linarith
  have hFsupportT : chapter06SupportWithin F T := by
    intro x hx
    have hx' := hFsupport hx
    constructor <;> linarith [hx'.1, hx'.2, hRη, hRF_nonneg]
  have hconv_support : ∀ n : ℕ,
      Function.support (chapter06SmoothedConvolution η F n) ⊆ Icc (-T) T := by
    intro n x hx
    have hxsum : x ∈ Function.support (η n) + Function.support F := by
      apply (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure ℝ)) (f := η n) (g := F))
      change chapter06SmoothedConvolution η F n x ≠ 0 at hx
      exact hx
    rcases hxsum with ⟨a, ha, b, hb, rfl⟩
    have ha' := hηsupport n ha
    have hb' := hFsupport hb
    exact ⟨by linarith [ha'.1, hb'.1], by linarith [ha'.2, hb'.2]⟩
  have hGsupport : ∀ n : ℕ, Function.support (G n) ⊆ Icc (-T) T := by
    intro n x hx
    change G n x ≠ 0 at hx
    have hxconv : chapter06SmoothedConvolution η F n x ≠ 0 := by
      intro hxzero
      apply hx
      simp [G, chapter06SmoothedTestFunction, hxzero]
    exact hconv_support n hxconv
  let B : ℕ := Nat.ceil (Real.exp T)
  let M : ℕ := Nat.ceil (T / Real.log (2 : ℝ))
  let SP : Set (Chapter06PrimeIdeal K) :=
    {P | chapter06PrimeIdealNorm P ≤ B}
  let U : Set Chapter06PositiveExponent :=
    {m | m.1 ≤ M}
  let S : Set (Chapter06PrimePower K) := SP ×ˢ U
  have hSP : SP.Finite := by
    simpa [SP, B, chapter06PrimeIdealNorm, chapter03PrimeIdealNorm,
      chapter03AbsoluteIdealNorm] using
      (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
        (R := 𝓞 K) B)
  have hU : U.Finite := by
    simpa [U] using
      (Set.finite_le_nat M).preimage (by
        intro a _ b _ hab
        exact Subtype.ext hab)
  have hS : S.Finite := by
    exact hSP.prod hU
  have hterm_mem : ∀ {H : ℝ → ℝ},
      chapter06SupportWithin H T → ∀ q : Chapter06PrimePower K,
        chapter06PrimePowerTerm H q ≠ 0 → q ∈ S := by
    intro H hH q hterm
    change chapter06PrimeIdealNorm q.1 ≤ B ∧ q.2.1 ≤ M
    have hNgt : 1 < chapter06PrimeIdealNorm q.1 :=
      chapter03_prime_ideal_norm_gt_one q.1
    have hlog : 0 < Real.log (chapter06PrimeIdealNorm q.1 : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hNgt)
    have hHq : H ((q.2.1 : ℝ) *
        Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ≠ 0 := by
      intro hzero
      apply hterm
      simp [chapter06PrimePowerTerm, hzero]
    have hmem : ((q.2.1 : ℝ) *
        Real.log (chapter06PrimeIdealNorm q.1 : ℝ)) ∈ Function.support H := hHq
    have hbound : (q.2.1 : ℝ) *
        Real.log (chapter06PrimeIdealNorm q.1 : ℝ) ≤ T :=
      hH hmem |>.2
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
      have hN2nat : 2 ≤ chapter06PrimeIdealNorm q.1 := by omega
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
  have hsum_eq : ∀ {H : ℝ → ℝ}, chapter06SupportWithin H T →
      (∑' q : Chapter06PrimePower K, chapter06PrimePowerTerm H q) =
        ∑ q ∈ hS.toFinset, chapter06PrimePowerTerm H q := by
    intro H hH
    rw [tsum_eq_sum (s := hS.toFinset)]
    intro q hq
    by_contra hterm
    apply hq
    exact hS.mem_toFinset.mpr (hterm_mem hH q hterm)
  have hphi_tendsto : ∀ y : ℝ,
      Tendsto (fun n => chapter06SmoothedConvolution η F n y) atTop
        (𝓝 (F y)) := by
    intro y
    have hphi_cont : Continuous (fun x : ℝ => F (y - x)) := by
      exact hF.continuous.comp (continuous_const.sub continuous_id)
    have hphi_compact : HasCompactSupport (fun x : ℝ => F (y - x)) := by
      let e : ℝ ≃ₜ ℝ := (Homeomorph.neg ℝ).trans (Homeomorph.addLeft y)
      have he : IsClosedEmbedding (fun x : ℝ => y - x) := by
        convert e.isClosedEmbedding using 1
        ext x
        simp [e, sub_eq_add_neg]
      change HasCompactSupport (F ∘ fun x : ℝ => y - x)
      exact hF.compactSupport.comp_isClosedEmbedding he
    have hlim := hηconv (fun x : ℝ => F (y - x)) hphi_cont hphi_compact
    have heq : ∀ n, chapter06SmoothedConvolution η F n y =
        ∫ x : ℝ, η n x * F (y - x) := by
      intro n
      simp [chapter06SmoothedConvolution, chapter05Convolution,
        MeasureTheory.convolution_def]
    simpa only [heq, sub_zero] using hlim
  have hterm_tendsto : ∀ q : Chapter06PrimePower K,
      Tendsto (fun n => chapter06PrimePowerTerm (G n) q) atTop
        (𝓝 (chapter06PrimePowerTerm F q)) := by
    intro q
    let y : ℝ := (q.2.1 : ℝ) *
      Real.log (chapter06PrimeIdealNorm q.1 : ℝ)
    have hy := hphi_tendsto y
    have hGy : Tendsto (fun n => G n y) atTop (𝓝 (F y)) := by
      simpa [G, chapter06SmoothedTestFunction] using hcorr.mul hy
    simpa [chapter06PrimePowerTerm, y] using
      (tendsto_const_nhds.mul hGy)
  have hfinite : Tendsto
      (fun n => ∑ q ∈ hS.toFinset, chapter06PrimePowerTerm (G n) q) atTop
        (𝓝 (∑ q ∈ hS.toFinset, chapter06PrimePowerTerm F q)) := by
    exact tendsto_finsetSum _ (fun q _ => hterm_tendsto q)
  have hGsum : ∀ n : ℕ, chapter06PrimeContribution K (G n) =
      2 * ∑ q ∈ hS.toFinset, chapter06PrimePowerTerm (G n) q := by
    intro n
    unfold chapter06PrimeContribution
    rw [hsum_eq (hGsupport n)]
  have hFsum : chapter06PrimeContribution K F =
      2 * ∑ q ∈ hS.toFinset, chapter06PrimePowerTerm F q := by
    unfold chapter06PrimeContribution
    rw [hsum_eq hFsupportT]
  have hresult : Tendsto (fun n => chapter06PrimeContribution K (G n)) atTop
      (𝓝 (chapter06PrimeContribution K F)) := by
    simpa only [hGsum, hFsum] using
      (tendsto_const_nhds.mul hfinite)
  simpa [G] using hresult

private theorem chapter06_basically_admissible_lipschitz_bound
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
      |F x - F y| ≤ C * |x - y| := by
  rcases hF.oneSidedDerivativeBV with
    ⟨leftDerivative, rightDerivative, hleft, hright, hleftBV, hrightBV⟩
  change eVariationOn rightDerivative (Set.univ : Set ℝ) ≠ (⊤ : ENNReal)
      at hrightBV
  let V : ENNReal := eVariationOn rightDerivative (Set.univ : Set ℝ)
  let C : ℝ := |rightDerivative 0| + V.toReal
  have hV : V ≠ (⊤ : ENNReal) := by
    exact hrightBV
  have hright_bound : ∀ x : ℝ, ‖rightDerivative x‖ ≤ C := by
    intro x
    have hdist := eVariationOn.edist_le rightDerivative
      (s := (Set.univ : Set ℝ)) (x := x) (y := 0) (by simp) (by simp)
    have hdist' : ENNReal.ofReal |rightDerivative x - rightDerivative 0| ≤ V := by
      simpa [V, edist_dist, Real.dist_eq] using hdist
    have habs : |rightDerivative x - rightDerivative 0| ≤ V.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hV).mp hdist'
    change |rightDerivative x| ≤ C
    calc
      |rightDerivative x| =
          |(rightDerivative x - rightDerivative 0) + rightDerivative 0| := by
            congr 1
            ring
      _ ≤ |rightDerivative x - rightDerivative 0| + |rightDerivative 0| :=
        abs_add_le _ _
      _ ≤ V.toReal + |rightDerivative 0| := by
        gcongr
      _ = C := by
        dsimp [C]
        ring
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x y
  by_cases hxy : x ≤ y
  · have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := F) (f' := rightDerivative) (a := x) (b := y)
      hF.continuous.continuousOn
      (fun z hz => hright z)
      (fun z hz => by simpa [Real.norm_eq_abs] using hright_bound z)
      y ⟨hxy, le_rfl⟩
    simpa [Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr hxy)] using hseg
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
      (f := F) (f' := rightDerivative) (a := y) (b := x)
      hF.continuous.continuousOn
      (fun z hz => hright z)
      (fun z hz => by simpa [Real.norm_eq_abs] using hright_bound z)
      x ⟨hyx, le_rfl⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hyx)] using hseg

theorem chapter06_smoothed_archimedean_terms_converge
    {η : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hη : chapter06ApproximateIdentity η)
    (hF : Chapter06BasicallyAdmissible F) :
    Tendsto (fun n => chapter06A (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06A F)) ∧
      Tendsto (fun n => chapter06B (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06B F)) ∧
      Tendsto (fun n => chapter06C (chapter06SmoothedTestFunction η F n)) atTop
        (𝓝 (chapter06C F)) := by
  classical
  let G : ℕ → ℝ → ℝ :=
    fun n => chapter06SmoothedTestFunction η F n
  have hcorr : Tendsto
      (fun n : ℕ => chapter06OriginCorrectionFactor η F n) atTop (𝓝 1) :=
    chapter06_origin_correction_factor_tendsto_one hη hF
  have hrange := Metric.isBounded_range_of_tendsto
    (fun n : ℕ => chapter06OriginCorrectionFactor η F n) hcorr
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hrange
  have hcorr_bound : ∀ n : ℕ,
      ‖chapter06OriginCorrectionFactor η F n‖ ≤ M := by
    intro n
    have hn := hM (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hn
  have hMnonneg : 0 ≤ M := by
    exact (norm_nonneg _).trans (hcorr_bound 0)
  obtain ⟨L, hLnonneg, hL⟩ :=
    chapter06_basically_admissible_lipschitz_bound hF
  have hηdata := hη
  rcases hηdata with ⟨hηint, hηcompact, hηsupport, hηdiff, hηnonneg,
    hηeven, hηnorm, hηconv⟩
  have hconv_tendsto : ∀ x : ℝ,
      Tendsto (fun n => chapter06SmoothedConvolution η F n x) atTop
        (𝓝 (F x)) := by
    intro x
    have hphi_cont : Continuous (fun y : ℝ => F (x - y)) := by
      exact hF.continuous.comp (continuous_const.sub continuous_id)
    have hphi_compact : HasCompactSupport (fun y : ℝ => F (x - y)) := by
      let e : ℝ ≃ₜ ℝ := (Homeomorph.neg ℝ).trans (Homeomorph.addLeft x)
      have he : IsClosedEmbedding (fun y : ℝ => x - y) := by
        convert e.isClosedEmbedding using 1
        ext y
        simp [e, sub_eq_add_neg]
      change HasCompactSupport (F ∘ fun y : ℝ => x - y)
      exact hF.compactSupport.comp_isClosedEmbedding he
    have hlim := hηconv (fun y : ℝ => F (x - y)) hphi_cont hphi_compact
    have heq : ∀ n, chapter06SmoothedConvolution η F n x =
        ∫ y : ℝ, η n y * F (x - y) := by
      intro n
      simp [chapter06SmoothedConvolution, chapter05Convolution,
        MeasureTheory.convolution_def]
    simpa only [heq, sub_zero] using hlim
  have hG_tendsto : ∀ x : ℝ,
      Tendsto (fun n => G n x) atTop (𝓝 (F x)) := by
    intro x
    have hmul := hcorr.mul (hconv_tendsto x)
    simpa [G, chapter06SmoothedTestFunction] using hmul
  obtain ⟨BF₀, hBF₀⟩ :=
    hF.compactSupport.exists_bound_of_continuous hF.continuous
  let BF : ℝ := max BF₀ 0
  have hBFnonneg : 0 ≤ BF := by
    dsimp [BF]
    exact le_max_right _ _
  have hBF : ∀ x : ℝ, |F x| ≤ BF := by
    intro x
    change ‖F x‖ ≤ BF
    exact (hBF₀ x).trans (le_max_left _ _)
  have hconv_integrable : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => η n y * F (x - y)) := by
    intro n x
    apply Integrable.mono' ((hηint n).const_mul BF)
    · exact
        (((hηdiff n).continuous.mul
          (hF.continuous.comp (continuous_const.sub continuous_id))).measurable
          ).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (hηnonneg n y)]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (hBF (x - y)) (hηnonneg n y))
  have hconv_eq : ∀ n : ℕ, ∀ x : ℝ,
      chapter06SmoothedConvolution η F n x =
        ∫ y : ℝ, η n y * F (x - y) := by
    intro n x
    simp [chapter06SmoothedConvolution, chapter05Convolution,
      MeasureTheory.convolution_def]
  have hconv_bound : ∀ n : ℕ, ∀ x : ℝ,
      |chapter06SmoothedConvolution η F n x| ≤ BF := by
    intro n x
    rw [hconv_eq n x]
    have hnorm := norm_integral_le_of_norm_le
      (f := fun y : ℝ => η n y * F (x - y))
      (g := fun y : ℝ => BF * η n y)
      ((hηint n).const_mul BF) (by
        filter_upwards [] with y
        rw [Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (hηnonneg n y)]
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left (hBF (x - y)) (hηnonneg n y)))
    calc
      |∫ y : ℝ, η n y * F (x - y)| =
          ‖∫ y : ℝ, η n y * F (x - y)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ y : ℝ, BF * η n y := hnorm
      _ = BF := by
        rw [integral_const_mul, hηnorm n]
        simp
  have hconv_lipschitz : ∀ n : ℕ, ∀ x y : ℝ,
      |chapter06SmoothedConvolution η F n x -
          chapter06SmoothedConvolution η F n y| ≤ L * |x - y| := by
    intro n x y
    have hdiff : Integrable (fun z : ℝ =>
        η n z * (F (x - z) - F (y - z))) := by
      have hfun : (fun z : ℝ =>
          η n z * (F (x - z) - F (y - z))) =
          (fun z : ℝ => η n z * F (x - z)) -
            (fun z : ℝ => η n z * F (y - z)) := by
        funext z
        simp only [Pi.sub_apply]
        ring
      rw [hfun]
      exact (hconv_integrable n x).sub (hconv_integrable n y)
    have heq : chapter06SmoothedConvolution η F n x -
        chapter06SmoothedConvolution η F n y =
        ∫ z : ℝ, η n z * (F (x - z) - F (y - z)) := by
      rw [hconv_eq n x, hconv_eq n y]
      rw [← integral_sub (hconv_integrable n x) (hconv_integrable n y)]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [heq]
    have hnorm := norm_integral_le_of_norm_le
      (f := fun z : ℝ => η n z * (F (x - z) - F (y - z)))
      (g := fun z : ℝ => (L * |x - y|) * η n z)
      ((hηint n).const_mul (L * |x - y|)) (by
        filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hηnonneg n z)]
        calc
          η n z * |F (x - z) - F (y - z)| ≤
              η n z * (L * |(x - z) - (y - z)|) :=
            mul_le_mul_of_nonneg_left
              (hL (x - z) (y - z)) (hηnonneg n z)
          _ = (L * |x - y|) * η n z := by
            rw [show (x - z) - (y - z) = x - y by ring]
            ring
      )
    calc
      |∫ z : ℝ, η n z * (F (x - z) - F (y - z))| =
          ‖∫ z : ℝ, η n z * (F (x - z) - F (y - z))‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ z : ℝ, (L * |x - y|) * η n z := hnorm
      _ = L * |x - y| := by
        rw [integral_const_mul, hηnorm n]
        simp
  have hG_bound : ∀ n : ℕ, ∀ x : ℝ, |G n x| ≤ M * BF := by
    intro n x
    change |chapter06OriginCorrectionFactor η F n *
      chapter06SmoothedConvolution η F n x| ≤ M * BF
    rw [abs_mul]
    calc
      |chapter06OriginCorrectionFactor η F n| *
          |chapter06SmoothedConvolution η F n x| ≤ M * BF := by
            gcongr
            · simpa [Real.norm_eq_abs] using hcorr_bound n
            · exact hconv_bound n x
      _ = M * BF := rfl
  have hG_lipschitz : ∀ n : ℕ, ∀ x y : ℝ,
      |G n x - G n y| ≤ (M * L) * |x - y| := by
    intro n x y
    change |chapter06OriginCorrectionFactor η F n *
        chapter06SmoothedConvolution η F n x -
      chapter06OriginCorrectionFactor η F n *
        chapter06SmoothedConvolution η F n y| ≤ _
    rw [← mul_sub, abs_mul]
    calc
      |chapter06OriginCorrectionFactor η F n| *
          |chapter06SmoothedConvolution η F n x -
            chapter06SmoothedConvolution η F n y| ≤
          M * (L * |x - y|) := by
            gcongr
            · simpa [Real.norm_eq_abs] using hcorr_bound n
            · exact hconv_lipschitz n x y
      _ = (M * L) * |x - y| := by ring
  obtain ⟨Rη, hRη, hηsupport⟩ := hηsupport
  obtain ⟨RF₀, hRF⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      hF.compactSupport.isBounded
  let RF : ℝ := max RF₀ 0
  have hRFnonneg : 0 ≤ RF := by
    dsimp [RF]
    exact le_max_right _ _
  have hFsupport : Function.support F ⊆ Icc (-RF) RF := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : ℝ) RF₀ :=
      hRF (subset_closure hx)
    have habs : |x| ≤ RF₀ := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hx'
    exact abs_le.mp (habs.trans (le_max_left _ _))
  let T : ℝ := Rη + RF
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    linarith
  have hGsupport : ∀ n : ℕ, Function.support (G n) ⊆ Icc (-T) T := by
    intro n x hx
    change G n x ≠ 0 at hx
    have hxconv : chapter06SmoothedConvolution η F n x ≠ 0 := by
      intro hxzero
      apply hx
      simp [G, chapter06SmoothedTestFunction, hxzero]
    have hxsum : x ∈ Function.support (η n) + Function.support F := by
      apply (MeasureTheory.support_convolution_subset
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure ℝ)) (f := η n) (g := F))
      change chapter06SmoothedConvolution η F n x ≠ 0
      exact hxconv
    rcases hxsum with ⟨a, ha, b, hb, rfl⟩
    have ha' := hηsupport n ha
    have hb' := hFsupport hb
    exact ⟨by linarith [ha'.1, hb'.1], by linarith [ha'.2, hb'.2]⟩
  have hGcontinuous : ∀ n : ℕ, Continuous (G n) := by
    intro n
    dsimp [G]
    exact (chapter06_smoothed_test_function_smooth_compact hη hF n).2.1.continuous
  have hcosh_bound : ∀ x : ℝ, x ∈ Icc (0 : ℝ) T →
      Real.cosh (x / 2) ≤ Real.exp (T / 2) := by
    intro x hx
    have hneg : -(x / 2) ≤ x / 2 := by linarith [hx.1]
    have hleft : Real.exp (-(x / 2)) ≤ Real.exp (x / 2) :=
      Real.exp_le_exp.mpr hneg
    have hright : Real.exp (x / 2) ≤ Real.exp (T / 2) :=
      Real.exp_le_exp.mpr (by linarith [hx.2])
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (x / 2), Real.exp_pos (T / 2)]
  let QA : ℝ := M * BF * Real.exp (T / 2)
  have hQAnonneg : 0 ≤ QA := by
    dsimp [QA]
    positivity
  let boundA : ℝ → ℝ := (Icc (0 : ℝ) T).indicator (fun _ => QA)
  have hboundA : IntegrableOn boundA (Ioi (0 : ℝ)) := by
    dsimp [boundA]
    have hconst : IntegrableOn (fun _ : ℝ => QA) (Icc (0 : ℝ) T) :=
      (continuous_const : Continuous (fun _ : ℝ => QA)).continuousOn
        |>.integrableOn_compact isCompact_Icc
    exact (hconst.integrable_indicator measurableSet_Icc).integrableOn
  have hA_meas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable
        (fun x : ℝ => G n x * Real.cosh (x / 2))
          (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with n
    have hmeas : Measurable (fun x : ℝ => G n x * Real.cosh (x / 2)) :=
      ((hGcontinuous n).mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).measurable
    exact hmeas.aestronglyMeasurable
  have hA_bound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖G n x * Real.cosh (x / 2)‖ ≤ boundA x := by
    filter_upwards [] with n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hxzero : G n x = 0
    · by_cases hxIcc : x ∈ Icc (0 : ℝ) T
      · simp [hxzero, boundA, hxIcc]
        exact hQAnonneg
      · simp [hxzero, boundA, hxIcc]
    · have hxG := hGsupport n hxzero
      have hxIcc : x ∈ Icc (0 : ℝ) T := ⟨le_of_lt hx, hxG.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _)]
      change |G n x| * Real.cosh (x / 2) ≤
        (Icc (0 : ℝ) T).indicator (fun _ => QA) x
      rw [Set.indicator_of_mem hxIcc]
      exact mul_le_mul (hG_bound n x) (hcosh_bound x hxIcc)
        (Real.cosh_pos _).le (by positivity)
  have hA_pointwise : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => G n x * Real.cosh (x / 2)) atTop
        (𝓝 (F x * Real.cosh (x / 2))) := by
    filter_upwards [] with x
    exact (hG_tendsto x).mul_const (Real.cosh (x / 2))
  have hA_limit :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (n : ℕ) (x : ℝ) => G n x * Real.cosh (x / 2))
      (f := fun x : ℝ => F x * Real.cosh (x / 2))
      boundA hA_meas hA_bound hboundA hA_pointwise
  have hA : Tendsto (fun n => chapter06A (G n)) atTop
      (𝓝 (chapter06A F)) := by
    simpa [G, chapter06A] using hA_limit
  have hCbasecont : Continuous
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) := by
    apply Continuous.div continuous_const
      (continuous_const.mul (Real.continuous_cosh.comp
        (continuous_id.div_const 2)))
    intro x
    exact (mul_pos (by norm_num) (Real.cosh_pos _)).ne'
  have hCbaseSmall : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioc (0 : ℝ) 1) := by
    exact (hCbasecont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hCoshExpBound : ∀ x ∈ Ioi (0 : ℝ),
      Real.exp (x / 2) ≤ 2 * Real.cosh (x / 2) := by
    intro x hx
    rw [Real.cosh_eq]
    nlinarith [Real.exp_nonneg (-(x / 2))]
  have hExpTail : IntegrableOn
      (fun x : ℝ => Real.exp (-x / 2)) (Ioi (1 : ℝ)) := by
    convert (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 1)
      using 1
    ext x
    congr 1
    ring
  have hCbaseTail : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioi (1 : ℝ)) := by
    apply hExpTail.integrable.mono'
    · exact hCbasecont.measurable.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := lt_trans (by norm_num) hx
      have hdenpos : 0 < 2 * Real.cosh (x / 2) := by positivity
      have hbase_nonneg : 0 ≤ 1 / (2 * Real.cosh (x / 2)) :=
        div_nonneg (by norm_num) hdenpos.le
      rw [Real.norm_eq_abs, abs_of_nonneg hbase_nonneg]
      apply (div_le_iff₀ hdenpos).2
      have hprod : 1 ≤ Real.exp (-x / 2) * (2 * Real.cosh (x / 2)) := by
        calc
          1 = Real.exp (-x / 2) * Real.exp (x / 2) := by
            rw [← Real.exp_add]
            ring_nf
            simp
          _ ≤ Real.exp (-x / 2) * (2 * Real.cosh (x / 2)) :=
            mul_le_mul_of_nonneg_left (hCoshExpBound x hxpos)
              (by positivity)
      exact hprod
  have hCbase : IntegrableOn
      (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioi (0 : ℝ)) := by
    have hu := hCbaseSmall.union hCbaseTail
    have hsub : Ioi (0 : ℝ) ⊆ Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
      intro x hx
      by_cases hle : x ≤ 1
      · exact Or.inl ⟨hx, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    exact hu.mono_set hsub
  let Qtail : ℝ := 1 + M * BF + BF
  have hQtailnonneg : 0 ≤ Qtail := by
    dsimp [Qtail]
    positivity
  let Qc : ℝ := Qtail
  have hQc : 0 ≤ Qc := by
    dsimp [Qc]
    exact hQtailnonneg
  let boundC : ℝ → ℝ := fun x =>
    Qc * (1 / (2 * Real.cosh (x / 2)))
  have hboundC : IntegrableOn boundC (Ioi (0 : ℝ)) := by
    dsimp [boundC]
    exact hCbase.const_mul Qc
  have hC_meas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable
        (fun x : ℝ => (1 - G n x) / (2 * Real.cosh (x / 2)))
          (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with n
    have hcont : Continuous
        (fun x : ℝ => (1 - G n x) / (2 * Real.cosh (x / 2))) := by
      apply Continuous.div (continuous_const.sub (hGcontinuous n))
        (continuous_const.mul (Real.continuous_cosh.comp
          (continuous_id.div_const 2)))
      intro x
      exact (mul_pos (by norm_num) (Real.cosh_pos _)).ne'
    have hmeas : Measurable
        (fun x : ℝ => (1 - G n x) / (2 * Real.cosh (x / 2))) :=
      hcont.measurable
    exact hmeas.aestronglyMeasurable
  have hC_bound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(1 - G n x) / (2 * Real.cosh (x / 2))‖ ≤ boundC x := by
    filter_upwards [] with n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxden : 0 < 2 * Real.cosh (x / 2) := by positivity
    have hnum : |1 - G n x| ≤ Qtail := by
      have htriangle : |1 - G n x| ≤ 1 + |G n x| := by
        calc
          |1 - G n x| = |1 + -(G n x)| := by congr 1
          _ ≤ |1| + |-(G n x)| := abs_add_le _ _
          _ = 1 + |G n x| := by simp
      dsimp [Qtail]
      linarith [hG_bound n x, hBFnonneg]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxden]
    change |1 - G n x| / (2 * Real.cosh (x / 2)) ≤
      Qc * (1 / (2 * Real.cosh (x / 2)))
    have hqc : Qc * (1 / (2 * Real.cosh (x / 2))) =
        Qtail / (2 * Real.cosh (x / 2)) := by
      dsimp [Qc]
      simp [div_eq_mul_inv]
    rw [hqc]
    exact div_le_div_of_nonneg_right hnum hxden.le
  have hC_pointwise : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => (1 - G n x) / (2 * Real.cosh (x / 2))) atTop
        (𝓝 ((1 - F x) / (2 * Real.cosh (x / 2)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hcont : Continuous
        (fun z : ℝ => (1 - z) / (2 * Real.cosh (x / 2))) := by
      exact (continuous_const.sub continuous_id).div_const _
    exact hcont.continuousAt.tendsto.comp (hG_tendsto x)
  have hC_limit :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (n : ℕ) (x : ℝ) =>
        (1 - G n x) / (2 * Real.cosh (x / 2)))
      (f := fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2)))
      boundC hC_meas hC_bound hboundC hC_pointwise
  have hC : Tendsto (fun n => chapter06C (G n)) atTop
      (𝓝 (chapter06C F)) := by
    simpa [G, chapter06C] using hC_limit
  let c : ℝ := 1 - Real.exp (-1)
  have hcpos : 0 < c := by
    dsimp [c]
    have he : Real.exp (-1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  have hSinhBound : ∀ x ∈ Ioi (1 : ℝ),
      c * Real.exp (x / 2) ≤ 2 * Real.sinh (x / 2) := by
    intro x hx
    change 1 < x at hx
    have hexp : Real.exp (-x) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      linarith [hx]
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
  have hBtail : IntegrableOn
      (fun x : ℝ => Qtail / (2 * Real.sinh (x / 2))) (Ioi (1 : ℝ)) := by
    have hmajor : IntegrableOn
        (fun x : ℝ => (c⁻¹ * Qtail) * Real.exp (-x / 2)) (Ioi (1 : ℝ)) := by
      show Integrable (fun x : ℝ =>
          (c⁻¹ * Qtail) * Real.exp (-x / 2))
        (volume.restrict (Ioi (1 : ℝ)))
      simpa [mul_assoc] using hExpTail.integrable.const_mul (c⁻¹ * Qtail)
    apply hmajor.integrable.mono'
    · have hcont : ContinuousOn
          (fun x : ℝ => Qtail / (2 * Real.sinh (x / 2))) (Ioi (1 : ℝ)) := by
        apply ContinuousOn.div continuousOn_const
          (continuous_const.mul (Real.continuous_sinh.comp
            (continuous_id.div_const 2))).continuousOn
        intro x hx
        have hxpos : 0 < x := lt_trans (by norm_num) hx
        exact (mul_pos (by norm_num)
          (Real.sinh_pos_iff.mpr (div_pos hxpos (by norm_num)))).ne'
      have hmeas : Measurable
          (fun x : ℝ => Qtail / (2 * Real.sinh (x / 2))) :=
        measurable_const.div
          (measurable_const.mul
            (Real.continuous_sinh.measurable.comp
              (measurable_id.div measurable_const)))
      exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := lt_trans (by norm_num) hx
      have hdenpos : 0 < 2 * Real.sinh (x / 2) := by
        exact mul_pos (by norm_num)
          (Real.sinh_pos_iff.mpr (div_pos hxpos (by norm_num)))
      have hbase_nonneg : 0 ≤ Qtail / (2 * Real.sinh (x / 2)) :=
        div_nonneg hQtailnonneg hdenpos.le
      rw [Real.norm_eq_abs, abs_of_nonneg hbase_nonneg]
      apply (div_le_iff₀ hdenpos).2
      have hcoef : 0 ≤ c⁻¹ * Qtail * Real.exp (-x / 2) :=
        mul_nonneg (mul_nonneg (inv_nonneg.mpr hcpos.le) hQtailnonneg)
          (Real.exp_nonneg (-x / 2))
      have hmul := mul_le_mul_of_nonneg_left (hSinhBound x hx) hcoef
      calc
        Qtail = (c⁻¹ * Qtail * Real.exp (-x / 2)) *
            (c * Real.exp (x / 2)) := by
          calc
            Qtail = Qtail * (c⁻¹ * c) *
                (Real.exp (-x / 2) * Real.exp (x / 2)) := by
              rw [inv_mul_cancel₀ (ne_of_gt hcpos), ← Real.exp_add]
              have hxe : -x / 2 + x / 2 = 0 := by ring
              rw [hxe, Real.exp_zero]
              simp
            _ = (c⁻¹ * Qtail * Real.exp (-x / 2)) *
                (c * Real.exp (x / 2)) := by ring_nf
        _ ≤ (c⁻¹ * Qtail * Real.exp (-x / 2)) *
            (2 * Real.sinh (x / 2)) := hmul
  let D : ℝ := M * L + L
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  let boundB : ℝ → ℝ :=
    (Icc (0 : ℝ) 1).indicator (fun _ => D) +
      (Ioi (1 : ℝ)).indicator
        (fun x => Qtail / (2 * Real.sinh (x / 2)))
  have hBsmallFull : Integrable
      ((Icc (0 : ℝ) 1).indicator (fun _ => D)) := by
    have hconst : IntegrableOn (fun _ : ℝ => D) (Icc (0 : ℝ) 1) :=
      (continuous_const : Continuous (fun _ : ℝ => D)).continuousOn
        |>.integrableOn_compact isCompact_Icc
    exact hconst.integrable_indicator measurableSet_Icc
  have hBtailFull : Integrable
      ((Ioi (1 : ℝ)).indicator
        (fun x => Qtail / (2 * Real.sinh (x / 2)))) := by
    exact hBtail.integrable_indicator measurableSet_Ioi
  have hboundB : IntegrableOn boundB (Ioi (0 : ℝ)) := by
    dsimp [boundB]
    exact (hBsmallFull.add hBtailFull).integrableOn
  have hB_meas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable
        (fun x : ℝ => (1 - G n x) / (2 * Real.sinh (x / 2)))
          (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with n
    have hmeas : Measurable
        (fun x : ℝ => (1 - G n x) / (2 * Real.sinh (x / 2))) := by
      exact (measurable_const.sub (hGcontinuous n).measurable).div
        (measurable_const.mul
          (Real.continuous_sinh.measurable.comp
            (measurable_id.div measurable_const)))
    exact hmeas.aestronglyMeasurable
  have hB_bound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(1 - G n x) / (2 * Real.sinh (x / 2))‖ ≤ boundB x := by
    have hne := chapter06_smoothed_origin_eventually_nonzero hη hF
    filter_upwards [hne] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hsmall : x ≤ 1
    · have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hx, hsmall⟩
      have hG0 : G n 0 = 1 := by
        simpa [G] using
          (chapter06_origin_correction_factor_apply_zero η F n hn)
      have hnum : |1 - G n x| ≤ D * x := by
        have hxpos : 0 < x := hx
        calc
          |1 - G n x| = |G n 0 - G n x| := by simp [hG0]
          _ ≤ M * L * |0 - x| := hG_lipschitz n 0 x
          _ = M * L * x := by
            rw [abs_of_nonpos (by linarith [hxpos])]
            ring
          _ ≤ D * x := by
            dsimp [D]
            nlinarith [mul_nonneg (le_of_lt hx) hLnonneg]
      have hdenpos : 0 < 2 * Real.sinh (x / 2) := by
        have hxpos : 0 < x := hx
        exact mul_pos (by norm_num)
          (Real.sinh_pos_iff.mpr (div_pos hxpos (by norm_num)))
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos hdenpos]
      change |1 - G n x| / (2 * Real.sinh (x / 2)) ≤ boundB x
      change |1 - G n x| / (2 * Real.sinh (x / 2)) ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => D) x +
          (Ioi (1 : ℝ)).indicator
            (fun x => Qtail / (2 * Real.sinh (x / 2))) x
      rw [Set.indicator_of_mem hxIcc]
      have htailzero : x ∉ Ioi (1 : ℝ) := by
        exact not_lt_of_ge hsmall
      rw [Set.indicator_of_notMem htailzero, add_zero]
      apply (div_le_iff₀ hdenpos).2
      have hsinh : x / 2 ≤ Real.sinh (x / 2) :=
        have hxpos : 0 < x := hx
        Real.self_le_sinh_iff.mpr (by linarith [hxpos])
      have hden : x ≤ 2 * Real.sinh (x / 2) := by
        linarith
      exact hnum.trans (mul_le_mul_of_nonneg_left hden hDnonneg)
    · have hxone : 1 < x := lt_of_not_ge hsmall
      have hdenpos : 0 < 2 * Real.sinh (x / 2) := by
        have hxpos : 0 < x := hx
        exact mul_pos (by norm_num)
          (Real.sinh_pos_iff.mpr (div_pos hxpos (by norm_num)))
      have hnum : |1 - G n x| ≤ Qtail := by
        have htriangle : |1 - G n x| ≤ 1 + |G n x| := by
          calc
            |1 - G n x| = |1 + -(G n x)| := by congr 1
            _ ≤ |1| + |-(G n x)| := abs_add_le _ _
            _ = 1 + |G n x| := by simp
        dsimp [Qtail]
        linarith [hG_bound n x, hBFnonneg]
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : 0 < 2 * Real.sinh (x / 2))]
      change |1 - G n x| / (2 * Real.sinh (x / 2)) ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => D) x +
          (Ioi (1 : ℝ)).indicator
            (fun x => Qtail / (2 * Real.sinh (x / 2))) x
      have hxIcc : x ∉ Icc (0 : ℝ) 1 := by
        intro hmem
        exact (not_le_of_gt hxone) hmem.2
      have htailmem : x ∈ Ioi (1 : ℝ) := hxone
      rw [Set.indicator_of_notMem hxIcc,
        Set.indicator_of_mem htailmem, zero_add]
      exact div_le_div_of_nonneg_right hnum hdenpos.le
  have hB_pointwise : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => (1 - G n x) / (2 * Real.sinh (x / 2))) atTop
        (𝓝 ((1 - F x) / (2 * Real.sinh (x / 2)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hcont : Continuous
        (fun z : ℝ => (1 - z) / (2 * Real.sinh (x / 2))) := by
      exact (continuous_const.sub continuous_id).div_const _
    exact hcont.continuousAt.tendsto.comp (hG_tendsto x)
  have hB_limit :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (n : ℕ) (x : ℝ) =>
        (1 - G n x) / (2 * Real.sinh (x / 2)))
      (f := fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2)))
      boundB hB_meas hB_bound hboundB hB_pointwise
  have hB : Tendsto (fun n => chapter06B (G n)) atTop
      (𝓝 (chapter06B F)) := by
    simpa [G, chapter06B] using hB_limit
  refine ⟨?_, ?_, ?_⟩
  · simpa [G] using hA
  · simpa [G] using hB
  · simpa [G] using hC

theorem chapter06_universal_expression_eq_formula_without_sums
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter06ZeroSpectrum K) (F : ℝ → ℝ) :
    chapter06ExplicitFormulaRightHandSide K Z F -
        chapter06ZeroContribution Z F - chapter06PrimeContribution K F =
      chapter06UniversalLowerBoundExpression K F := by
  simp [chapter06ExplicitFormulaRightHandSide,
    chapter06UniversalLowerBoundExpression]; ring

theorem chapter06_universal_expression_congr_of_ae
    (K : Type*) [Field K] [NumberField K] {F G : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F)
    (hG : Chapter06BasicallyAdmissible G)
    (hFG : F =ᵐ[volume] G) :
    chapter06UniversalLowerBoundExpression K F =
      chapter06UniversalLowerBoundExpression K G := by
  let _ := hF
  let _ := hG
  have hA : chapter06A F = chapter06A G := by
    unfold chapter06A
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  have hB : chapter06B F = chapter06B G := by
    unfold chapter06B
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  have hC : chapter06C F = chapter06C G := by
    unfold chapter06C
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hFG] with x hx
    rw [hx]
  unfold chapter06UniversalLowerBoundExpression
  rw [hA, hB, hC]

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
