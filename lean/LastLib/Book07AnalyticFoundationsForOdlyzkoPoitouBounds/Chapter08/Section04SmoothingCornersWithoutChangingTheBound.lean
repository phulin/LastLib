import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section03PositiveType
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section01TheThreeGoverningIntegrals
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Section02TheTriangularAutocorrelation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology Asymptotics Pointwise

noncomputable section

/-! ## 8.4 Smoothing corners without changing the bound -/

def Chapter08ApproximateIdentity (η : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, Integrable (η n)) ∧
    (∀ n, HasCompactSupport (η n)) ∧
    (∀ n, ContDiff ℝ ∞ (η n)) ∧
    (∀ n x, 0 ≤ η n x) ∧
    (∀ n x, η n (-x) = η n x) ∧
    (∀ n, ∫ x : ℝ, η n x = 1) ∧
    (∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ x : ℝ, η n x * φ x) atTop (𝓝 (φ 0)))

def chapter08SmoothedIntervalIndicator
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  chapter08Convolution (chapter08IntervalIndicator T) (η n)

/- The normalized autocorrelation below divides by its value at zero.  An abstract approximate
   identity need not have every member overlap the interval, so nonvanishing is recorded
   explicitly rather than being inferred from the weak convergence clause. -/
def Chapter08SmoothedAutocorrelationNondegenerate
    (η : ℕ → ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ n,
    chapter08Convolution (chapter08SmoothedIntervalIndicator η T n)
      (fun y => chapter08SmoothedIntervalIndicator η T n (-y)) 0 ≠ 0

def chapter08SmoothedUnconditionalTriangle
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  chapter08NormalizedAutocorrelation (chapter08SmoothedIntervalIndicator η T n)

def chapter08SmoothedUnconditionalTestFunction
    (η : ℕ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x => chapter08SmoothedUnconditionalTriangle η T n x / Real.cosh (x / 2)

def Chapter08SmoothingIntegralConvergence
    (η : ℕ → ℝ → ℝ) (T : ℝ) : Prop :=
  Tendsto (fun n => chapter08A (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08A (chapter08FUnconditionalTriangle T))) ∧
    Tendsto (fun n => chapter08B (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08B (chapter08FUnconditionalTriangle T))) ∧
    Tendsto (fun n => chapter08C (chapter08SmoothedUnconditionalTestFunction η T n))
      atTop (𝓝 (chapter08C (chapter08FUnconditionalTriangle T)))

theorem chapter08_smoothed_autocorrelation_nonnegative
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T) :
    ∀ n x, 0 ≤ chapter08SmoothedUnconditionalTriangle η T n x := by
  rcases hη with ⟨hηint, hηcompact, hηdiff, hηnonneg, hηeven, hηmass, hηlimit⟩
  have hinterval : -T / 2 ≤ T / 2 := by linarith [hT]
  have hind : ∀ y : ℝ, 0 ≤ chapter08IntervalIndicator T y := by
    intro y
    by_cases hT' : -T / 2 ≤ T / 2
    · by_cases hy : y ∈ Set.Icc (-T / 2) (T / 2)
      · simp [chapter08IntervalIndicator, hy]
      · simp [chapter08IntervalIndicator, hy]
    · exact (hT' hinterval).elim
  have hsmoothed : ∀ n y, 0 ≤ chapter08SmoothedIntervalIndicator η T n y := by
    intro n y
    unfold chapter08SmoothedIntervalIndicator chapter08Convolution
    apply integral_nonneg
    intro z
    exact mul_nonneg (hind z) (hηnonneg n (y - z))
  intro n x
  unfold chapter08SmoothedUnconditionalTriangle chapter08NormalizedAutocorrelation
  apply div_nonneg
  · unfold chapter08Convolution
    apply integral_nonneg
    intro y
    exact mul_nonneg (hsmoothed n y) (hsmoothed n (-(x - y)))
  · unfold chapter08Convolution
    apply integral_nonneg
    intro y
    simpa using mul_nonneg (hsmoothed n y) (hsmoothed n y)

theorem chapter08_smoothed_autocorrelation_positive_type
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T) :
    ∀ n, Chapter08PositiveType (chapter08SmoothedUnconditionalTriangle η T n) := by
  intro n
  rcases hη with ⟨hηint, hηcompact, hηdiff, hηnonneg, hηeven, hηmass, hηlimit⟩
  have hinterval_int : Integrable (chapter08IntervalIndicator T) volume := by
    rw [chapter08IntervalIndicator, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hinterval_compact : HasCompactSupport (chapter08IntervalIndicator T) := by
    refine (isCompact_Icc : IsCompact (Icc (-T / 2) (T / 2))).of_isClosed_subset
      (isClosed_tsupport _) ?_
    apply closure_minimal
    · intro x hx
      change chapter08IntervalIndicator T x ≠ 0 at hx
      by_contra hxm
      exact hx (by simp [chapter08IntervalIndicator, hxm])
    · exact isClosed_Icc
  let h : ℝ → ℝ := chapter08SmoothedIntervalIndicator η T n
  have hcont : Continuous h := by
    dsimp [h, chapter08SmoothedIntervalIndicator]
    exact hηcompact n |>.continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hinterval_int.locallyIntegrable
      (hηdiff n).continuous
  have hcompact : HasCompactSupport h := by
    dsimp [h]
    exact hinterval_compact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hηcompact n)
  have hL1 : Integrable h volume :=
    hcont.integrable_of_hasCompactSupport hcompact
  have hL2 : MemLp h 2 volume :=
    hcont.memLp_of_hasCompactSupport hcompact
  have hpt5 : Chapter05.Chapter05PositiveType (Chapter05.chapter05Autocorrelation h) :=
    Chapter05.chapter05_autocorrelation_is_positive_type h hL1 hL2
  have hpt5' := hpt5
  change Chapter05.Chapter05PositiveType
    (Chapter05.chapter05Convolution h (fun y => h (-y))) at hpt5'
  let G : ℝ → ℝ := chapter08Convolution h (fun y => h (-y))
  have hpt5G : Chapter05.Chapter05PositiveType G := by
    simpa [G, chapter08Convolution, Chapter05.chapter05Convolution] using hpt5'
  have heven : ∀ x : ℝ, h (-x) = h x := by
    intro x
    dsimp [h, chapter08SmoothedIntervalIndicator]
    apply convolution_neg_of_neg_eq
    · exact Filter.Eventually.of_forall (chapter08_interval_indicator_even hT)
    · exact Filter.Eventually.of_forall (hηeven n)
  have hGeven : Chapter08Even G := by
    intro x
    dsimp [G]
    rw [show (fun y : ℝ => h (-y)) = h by funext y; exact heven y]
    apply convolution_neg_of_neg_eq
    · exact Filter.Eventually.of_forall heven
    · exact Filter.Eventually.of_forall heven
  have hrawPT : Chapter08PositiveType G := by
    exact hpt5G
  have hnonneg_h : ∀ x : ℝ, 0 ≤ h x := by
    intro x
    dsimp [h, chapter08SmoothedIntervalIndicator]
    unfold chapter08Convolution
    apply integral_nonneg
    intro z
    have hz : 0 ≤ chapter08IntervalIndicator T z := by
      by_cases hz' : z ∈ Icc (-T / 2) (T / 2)
      · simp [chapter08IntervalIndicator, hz']
      · simp [chapter08IntervalIndicator, hz']
    exact mul_nonneg hz (hηnonneg n (x - z))
  by_cases hzero : G 0 = 0
  · have hzero_fun : chapter08SmoothedUnconditionalTriangle η T n =
        (fun _ : ℝ => 0) := by
      funext x
      simp [chapter08SmoothedUnconditionalTriangle, chapter08NormalizedAutocorrelation,
        h, G, hzero]
    rw [hzero_fun]
    exact ⟨continuous_zero,
      (by
        have hz : (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) := by
          funext x
          rfl
        rw [hz]
        exact integrable_zero ℝ ℝ volume),
      (by
        intro t
        rw [← chapter08_fourier_transform_eq_chapter05 (fun _ : ℝ => 0) t]
        simp [chapter08FourierTransform])⟩
  · have hGzero_nonneg : 0 ≤ G 0 := by
      dsimp [G]
      unfold chapter08Convolution
      apply integral_nonneg
      intro y
      simpa only [Pi.zero_apply, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg] using
        smul_nonneg (hnonneg_h y) (hnonneg_h y)
    have hGzero_pos : 0 < G 0 := lt_of_le_of_ne hGzero_nonneg (Ne.symm hzero)
    have hnormalized : chapter08SmoothedUnconditionalTriangle η T n =
        (fun x : ℝ => G x / G 0) := by
      funext x
      simp [chapter08SmoothedUnconditionalTriangle, chapter08NormalizedAutocorrelation,
        h, G]
    rw [hnormalized]
    have hNcont : Continuous (fun x : ℝ => G x / G 0) :=
      hpt5G.continuous.div_const _
    have hNint : Integrable (fun x : ℝ => G x / G 0) volume :=
      hpt5G.integrable.div_const _
    have hNeven : Chapter08Even (fun x : ℝ => G x / G 0) := by
      intro x
      change G (-x) / G 0 = G x / G 0
      rw [hGeven x]
    refine ⟨hNcont, hNint, ?_⟩
    intro t
    have hfourier :=
      chapter08_fourier_transform_eq_cosine_of_even hNint hNeven t
    have hre : (chapter08FourierTransform (fun x : ℝ => G x / G 0) t).re =
        chapter08CosineTransform (fun x : ℝ => G x / G 0) t := by
      rw [hfourier]
      simp
    have him : (chapter08FourierTransform (fun x : ℝ => G x / G 0) t).im = 0 := by
      rw [hfourier]
      simp
    have hcos : 0 ≤ chapter08CosineTransform (fun x : ℝ => G x / G 0) t := by
      unfold chapter08CosineTransform
      have hscale : (fun x : ℝ => (G x / G 0) * Real.cos (t * x)) =
          (fun x : ℝ => (G x * Real.cos (t * x)) / G 0) := by
        funext x
        field_simp
      rw [hscale, integral_div]
      have hGfourier :=
        chapter08_fourier_transform_eq_cosine_of_even hrawPT.integrable hGeven t
      have hGre : (chapter08FourierTransform G t).re = chapter08CosineTransform G t := by
        rw [hGfourier]
        simp
      have hGtransform := hrawPT.transformNonnegative t
      rw [← chapter08_fourier_transform_eq_chapter05 G t] at hGtransform
      have hGcos : 0 ≤ chapter08CosineTransform G t := by
        rw [← hGre]
        exact hGtransform.2
      exact div_nonneg hGcos hGzero_nonneg
    have hcustom :
        0 ≤ (chapter08FourierTransform (fun x : ℝ => G x / G 0) t).re ∧
          (chapter08FourierTransform (fun x : ℝ => G x / G 0) t).im = 0 := by
      exact ⟨by rw [hre]; exact hcos, him⟩
    rw [← chapter08_fourier_transform_eq_chapter05
      (fun x : ℝ => G x / G 0) t]
    exact ⟨hcustom.2, hcustom.1⟩

theorem chapter08_smoothed_unconditional_admissible
    {η : ℕ → ℝ → ℝ} (hη : Chapter08ApproximateIdentity η)
    {T : ℝ} (hT : 0 < T)
    (hdenom : Chapter08SmoothedAutocorrelationNondegenerate η T) :
    ∀ n, Chapter08UnconditionallyAdmissible
      (chapter08SmoothedUnconditionalTestFunction η T n) := by
  intro n
  have hpositive := chapter08_smoothed_autocorrelation_positive_type hη hT n
  have hnonnegative := chapter08_smoothed_autocorrelation_nonnegative hη hT n
  rcases hη with ⟨hηint, hηcompact, hηdiff, hηnonneg, hηeven, hηmass, hηlimit⟩
  have hinterval_int : Integrable (chapter08IntervalIndicator T) volume := by
    rw [chapter08IntervalIndicator, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hinterval_compact : HasCompactSupport (chapter08IntervalIndicator T) := by
    refine (isCompact_Icc : IsCompact (Icc (-T / 2) (T / 2))).of_isClosed_subset
      (isClosed_tsupport _) ?_
    apply closure_minimal
    · intro x hx
      change chapter08IntervalIndicator T x ≠ 0 at hx
      by_contra hxm
      exact hx (by simp [chapter08IntervalIndicator, hxm])
    · exact isClosed_Icc
  let h : ℝ → ℝ := chapter08SmoothedIntervalIndicator η T n
  have hcont : Continuous h := by
    dsimp [h, chapter08SmoothedIntervalIndicator]
    exact hηcompact n |>.continuous_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hinterval_int.locallyIntegrable
      (hηdiff n).continuous
  have hcompact : HasCompactSupport h := by
    dsimp [h]
    exact hinterval_compact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hηcompact n)
  have hL1 : Integrable h volume :=
    hcont.integrable_of_hasCompactSupport hcompact
  have hdiff : ContDiff ℝ ∞ h := by
    dsimp [h, chapter08SmoothedIntervalIndicator]
    exact hηcompact n |>.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hinterval_int.locallyIntegrable (hηdiff n)
  have heven : ∀ x : ℝ, h (-x) = h x := by
    intro x
    dsimp [h, chapter08SmoothedIntervalIndicator]
    apply convolution_neg_of_neg_eq
    · exact Filter.Eventually.of_forall (chapter08_interval_indicator_even hT)
    · exact Filter.Eventually.of_forall (hηeven n)
  let G : ℝ → ℝ := chapter08Convolution h (fun y => h (-y))
  have hG_eq : G = chapter08Convolution h h := by
    funext x
    dsimp [G]
    rw [show (fun y => h (-y)) = h by funext y; exact heven y]
  have hGcompact : HasCompactSupport G := by
    rw [hG_eq]
    exact hcompact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcompact
  have hGdiff : ContDiff ℝ ∞ G := by
    rw [hG_eq]
    exact hcompact.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hdiff hL1.locallyIntegrable
  have hGeven : Chapter08Even G := by
    intro x
    dsimp [G]
    rw [show (fun y => h (-y)) = h by funext y; exact heven y]
    apply convolution_neg_of_neg_eq
    · exact Filter.Eventually.of_forall heven
    · exact Filter.Eventually.of_forall heven
  have hGzero : G 0 ≠ 0 := by
    simpa [G, h, chapter08SmoothedIntervalIndicator] using hdenom n
  let F : ℝ → ℝ := fun x => G x / G 0 / Real.cosh (x / 2)
  have hFdiff : ContDiff ℝ ∞ F := by
    dsimp [F]
    apply (hGdiff.div_const (G 0)).div
      (by fun_prop)
    intro x
    exact ne_of_gt (Real.cosh_pos _)
  have hFcompact : HasCompactSupport F := by
    have h1 := hGcompact.mul_right (f' := fun _ : ℝ => (G 0)⁻¹)
    have h2 := h1.mul_right (f' := fun x : ℝ => (Real.cosh (x / 2))⁻¹)
    dsimp [F]
    change HasCompactSupport
      ((fun x => G x * (G 0)⁻¹) * (fun x => (Real.cosh (x / 2))⁻¹))
    exact (hGcompact.mul_right (f' := fun _ : ℝ => (G 0)⁻¹)).mul_right
      (f' := fun x => (Real.cosh (x / 2))⁻¹)
  have hFeven : Chapter08Even F := by
    intro x
    dsimp [F]
    rw [hGeven x, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  have hFzero : F 0 = 1 := by
    dsimp [F]
    norm_num [hGzero]
  have hFpiecewise : Chapter08PiecewiseC2 F := by
    refine ⟨∅, ?_⟩
    intro x hx
    refine ⟨1, by norm_num, ?_⟩
    exact (hFdiff.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffOn
  have hD : ContDiff ℝ 1 (fun x : ℝ => deriv F x) := by
    have hpair : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ F p.1 : ℝ → ℝ) p.2) :=
      hFdiff.contDiff_fderiv_apply (m := 1)
        (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) + 1 ≤ ⊤ from le_top))
    have hcomp := hpair.comp (contDiff_id.prodMk (contDiff_const :
      ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))))
    simpa [Function.comp_def, fderiv_apply_one_eq_deriv] using hcomp
  have hFbv : Chapter08FirstDerivativeBoundedVariation F := by
    refine ⟨fun x => deriv F x, fun x => deriv F x, ?_, ?_, ?_⟩
    · intro a b
      exact hD.contDiffOn.absolutelyContinuousOnInterval.boundedVariationOn
    · intro a b
      exact hD.contDiffOn.absolutelyContinuousOnInterval.boundedVariationOn
    · intro x
      have hderiv : HasDerivAt F (deriv F x) x := by
        exact ((hFdiff.differentiable (by norm_num) x).hasDerivAt)
      exact ⟨hderiv.hasDerivWithinAt, hderiv.hasDerivWithinAt⟩
  have hForigin : IntegrableOn (fun x : ℝ => |1 - F x| / x) (Ioc 0 1) := by
    have hFcont : Continuous F := hFdiff.continuous
    have hFcont1 : ContDiffOn ℝ 1 F (Icc (0 : ℝ) 1) :=
      (hFdiff.of_le (by simp)).contDiffOn
    obtain ⟨K, hK⟩ := hFcont1.exists_lipschitzOnWith one_ne_zero
      (convex_Icc (0 : ℝ) 1) isCompact_Icc
    apply Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ))
      (s := Ioc (0 : ℝ) 1) (M := (K : ℝ))
      (ne_of_lt measure_Ioc_lt_top)
    · exact (measurable_const.sub hFcont.measurable).norm.div measurable_id |>.aemeasurable
        |>.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxpos : 0 < x := hx.1
      have hxone : x ≤ 1 := hx.2
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hxpos.le, hxone⟩
      have hzero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
      have hdist := hK.dist_le_mul x hxIcc 0 hzero_mem
      rw [hFzero] at hdist
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hxpos.le)]
      apply (div_le_iff₀ hxpos).2
      simpa only [Real.dist_eq, abs_sub_comm, abs_of_pos hxpos, sub_zero, mul_one] using hdist
  have hbasic : Chapter08BasicallyAdmissible F :=
    ⟨hFeven, hFdiff.continuous, hFcompact, hFpiecewise, hFbv, hFzero, hForigin⟩
  have hnormalized :
      chapter08SmoothedUnconditionalTriangle η T n = (fun x => G x / G 0) := by
    funext x
    simp [chapter08SmoothedUnconditionalTriangle, chapter08NormalizedAutocorrelation,
      h, G]
  have hN_even : Chapter08Even
      (chapter08SmoothedUnconditionalTriangle η T n) := by
    rw [hnormalized]
    intro x
    simp [hGeven x]
  refine ⟨?_, ?_⟩
  · change Chapter08BasicallyAdmissible F
    exact hbasic
  · refine ⟨chapter08SmoothedUnconditionalTriangle η T n, hN_even,
      hnonnegative, hpositive, ?_⟩
    intro x
    rfl

/- The source supplies a compactly supported smooth even nonnegative mass-one mollifier and a
   common support/majorant argument.  The interface below records the corresponding approximate
   identity data and exposes the three weighted integral limits explicitly. -/
theorem chapter08_smoothing_construction
    {T : ℝ} (hT : 0 < T) :
    ∃ η : ℕ → ℝ → ℝ,
      Chapter08ApproximateIdentity η ∧
        Chapter08SmoothedAutocorrelationNondegenerate η T ∧
        (∀ n, Chapter08UnconditionallyAdmissible
          (chapter08SmoothedUnconditionalTestFunction η T n)) ∧
        Chapter08SmoothingIntegralConvergence η T := by
  classical
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨T / (8 * (n + 1 : ℝ)), T / (4 * (n + 1 : ℝ)), by positivity, by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith⟩
  let η : ℕ → ℝ → ℝ := fun n => (b n).normed (volume : Measure ℝ)
  have hb_out : Tendsto (fun n : ℕ => (b n).rOut) atTop (𝓝 (0 : ℝ)) := by
    have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      simpa [Function.comp_def, Nat.cast_add] using
        ((tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1))
    have hd : Tendsto (fun n : ℕ => 4 * (n + 1 : ℝ)) atTop atTop :=
      hn.const_mul_atTop (by norm_num)
    simpa [b] using (Filter.Tendsto.const_div_atTop hd T)
  have hsupport : Tendsto (fun n : ℕ => Function.support (η n)) atTop
      (𝓝 (0 : ℝ)).smallSets := by
    simpa [η] using
      (ContDiffBump.tendsto_support_normed_smallSets (μ := (volume : Measure ℝ))
        (φ := b) hb_out)
  have hηint : ∀ n, Integrable (η n) := by
    intro n
    simpa [η] using (b n).integrable_normed
  have hηcompact : ∀ n, HasCompactSupport (η n) := by
    intro n
    simpa [η] using (b n).hasCompactSupport_normed
  have hηdiff : ∀ n, ContDiff ℝ ∞ (η n) := by
    intro n
    simpa [η] using (b n).contDiff_normed
  have hηnonneg : ∀ n x, 0 ≤ η n x := by
    intro n x
    simpa [η] using (b n).nonneg_normed x
  have hηeven : ∀ n x, η n (-x) = η n x := by
    intro n x
    simpa [η] using (b n).normed_neg x
  have hηmass : ∀ n, ∫ x : ℝ, η n x = 1 := by
    intro n
    simpa [η] using (b n).integral_normed
  have happrox : Chapter08ApproximateIdentity η := by
    refine ⟨hηint, hηcompact, hηdiff, hηnonneg, hηeven, hηmass, ?_⟩
    intro φ hφ hφc
    have hconv := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := (volume : Measure ℝ)) (φ := b) (g := φ) (l := atTop)
      hb_out hφ 0
    have heq : ∀ n : ℕ,
        (∫ x : ℝ, η n x * φ x) =
          (MeasureTheory.convolution ((b n).normed (volume : Measure ℝ)) φ
            (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure ℝ)) 0 := by
      intro n
      rw [convolution_eq_swap]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ContinuousLinearMap.lsmul_apply, zero_sub]
      change η n x * φ x = η n (-x) * φ x
      rw [hηeven n x]
    have heqfun :
        (fun n : ℕ => ∫ x : ℝ, η n x * φ x) =
          (fun n : ℕ =>
            (MeasureTheory.convolution ((b n).normed (volume : Measure ℝ)) φ
              (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure ℝ)) 0) := by
      funext n
      exact heq n
    rw [heqfun]
    exact hconv
  have hdenom : Chapter08SmoothedAutocorrelationNondegenerate η T := by
    intro n
    have hinterval_int : Integrable (chapter08IntervalIndicator T) volume := by
      rw [chapter08IntervalIndicator, integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const measure_Icc_lt_top.ne
    have hinterval_compact : HasCompactSupport (chapter08IntervalIndicator T) := by
      refine (isCompact_Icc : IsCompact (Icc (-T / 2) (T / 2))).of_isClosed_subset
        (isClosed_tsupport _) ?_
      apply closure_minimal
      · intro x hx
        change chapter08IntervalIndicator T x ≠ 0 at hx
        by_contra hxm
        exact hx (by simp [chapter08IntervalIndicator, hxm])
      · exact isClosed_Icc
    let h : ℝ → ℝ := chapter08SmoothedIntervalIndicator η T n
    have hcont : Continuous h := by
      dsimp [h, chapter08SmoothedIntervalIndicator]
      exact hηcompact n |>.continuous_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hinterval_int.locallyIntegrable
        (hηdiff n).continuous
    have hcompact : HasCompactSupport h := by
      dsimp [h]
      exact hinterval_compact.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hηcompact n)
    have hL1 : Integrable h volume :=
      hcont.integrable_of_hasCompactSupport hcompact
    have hL2 : MemLp h 2 volume :=
      hcont.memLp_of_hasCompactSupport hcompact
    have hinterval_integral : ∫ x : ℝ, chapter08IntervalIndicator T x = T := by
      rw [chapter08IntervalIndicator, integral_indicator measurableSet_Icc]
      rw [setIntegral_const, Real.volume_real_Icc]
      rw [max_eq_left (by linarith)]
      simp
      ring
    have h_integral : ∫ x : ℝ, h x = T := by
      dsimp [h, chapter08SmoothedIntervalIndicator, chapter08Convolution]
      rw [MeasureTheory.integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        hinterval_int (hηint n)]
      simp [hinterval_integral, hηmass n, ContinuousLinearMap.lsmul_apply]
    have hne : ¬ h =ᵐ[volume] (0 : ℝ → ℝ) := by
      intro hz
      have hz' : ∫ x : ℝ, h x = 0 := integral_eq_zero_of_ae hz
      linarith [h_integral, hT]
    have hpos : 0 < Chapter05.chapter05Autocorrelation h 0 :=
      Chapter05.chapter05_autocorrelation_apply_zero_pos h hL2 hne
    have hpos' : 0 < chapter08Convolution h (fun y => h (-y)) 0 := by
      change 0 < chapter08Convolution h (fun y => h (-y)) 0 at hpos
      exact hpos
    exact ne_of_gt hpos'
  refine ⟨η, happrox, hdenom, ?_, ?_⟩
  · intro n
    exact chapter08_smoothed_unconditional_admissible happrox hT hdenom n
  · classical
    let I : ℝ → ℝ := chapter08IntervalIndicator T
    let h : ℕ → ℝ → ℝ := fun n => chapter08SmoothedIntervalIndicator η T n
    let G : ℕ → ℝ → ℝ := fun n =>
      chapter08Convolution (h n) (fun y => h n (-y))
    let G₀ : ℝ → ℝ := chapter08Convolution I (fun y => I (-y))
    have hIint : Integrable I := by
      dsimp [I]
      rw [chapter08IntervalIndicator, integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const measure_Icc_lt_top.ne
    have hIlocal : LocallyIntegrable I := hIint.locallyIntegrable
    have hIcompact : HasCompactSupport I := by
      dsimp [I]
      refine (isCompact_Icc : IsCompact (Icc (-T / 2) (T / 2))).of_isClosed_subset
        (isClosed_tsupport _) ?_
      apply closure_minimal
      · intro x hx
        change chapter08IntervalIndicator T x ≠ 0 at hx
        by_contra hxm
        exact hx (by simp [chapter08IntervalIndicator, hxm])
      · exact isClosed_Icc
    have hI_nonneg : ∀ x, 0 ≤ I x := by
      intro x
      by_cases hx : x ∈ Icc (-T / 2) (T / 2)
      · simp [I, chapter08IntervalIndicator, hx]
      · simp [I, chapter08IntervalIndicator, hx]
    have hI_le_one : ∀ x, I x ≤ 1 := by
      intro x
      by_cases hx : x ∈ Icc (-T / 2) (T / 2)
      · simp [I, chapter08IntervalIndicator, hx]
      · simp [I, chapter08IntervalIndicator, hx]
    have hIeven : ∀ x, I (-x) = I x := by
      intro x
      exact chapter08_interval_indicator_even hT x
    have hrout : ∀ n, (b n).rOut = T / (4 * (n + 1 : ℝ)) := by
      intro n
      rfl
    have hrout_le : ∀ n, (b n).rOut ≤ T / 4 := by
      intro n
      rw [hrout]
      calc
        T / (4 * (n + 1 : ℝ)) ≤ T / (4 * (1 : ℝ)) := by
          gcongr
          norm_num
        _ = T / 4 := by ring
    have hswap : ∀ n x, h n x = chapter08Convolution (η n) I x := by
      intro n x
      dsimp [h, chapter08SmoothedIntervalIndicator, chapter08Convolution]
      rw [MeasureTheory.convolution_eq_swap]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [ContinuousLinearMap.lsmul_apply]
      ring
    have hcont : ∀ n, Continuous (h n) := by
      intro n
      dsimp [h, chapter08SmoothedIntervalIndicator]
      exact hηcompact n |>.continuous_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hIint.locallyIntegrable
        (hηdiff n).continuous
    have heven_h : ∀ n x, h n (-x) = h n x := by
      intro n x
      dsimp [h, chapter08SmoothedIntervalIndicator]
      apply convolution_neg_of_neg_eq
      · exact Filter.Eventually.of_forall (chapter08_interval_indicator_even hT)
      · exact Filter.Eventually.of_forall (hηeven n)
    have hle : ∀ n x, h n x ≤ 1 := by
      intro n x
      rw [hswap n x]
      change (∫ y : ℝ, η n y * I (x - y)) ≤ 1
      calc
        (∫ y : ℝ, η n y * I (x - y)) ≤ ∫ y : ℝ, η n y := by
          apply integral_mono_of_nonneg
          · filter_upwards [] with y
            exact mul_nonneg (hηnonneg n y) (hI_nonneg (x - y))
          · exact hηint n
          · filter_upwards [] with y
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (hI_le_one (x - y)) (hηnonneg n y))
        _ = 1 := hηmass n
    have hnonneg : ∀ n x, 0 ≤ h n x := by
      intro n x
      rw [hswap n x]
      change 0 ≤ ∫ y : ℝ, η n y * I (x - y)
      apply integral_nonneg
      intro y
      exact mul_nonneg (hηnonneg n y) (hI_nonneg (x - y))
    have hsupport : ∀ n, Function.support (h n) ⊆ Icc (-3 * T / 4) (3 * T / 4) := by
      intro n x hx
      have hxsum : x ∈ Function.support I + Function.support (η n) := by
        apply (MeasureTheory.support_convolution_subset
          (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℝ))
          (f := I) (g := η n))
        change chapter08Convolution I (η n) x ≠ 0 at hx
        exact hx
      rcases hxsum with ⟨a, ha, c, hc, rfl⟩
      have haI : a ∈ Icc (-T / 2) (T / 2) := by
        change I a ≠ 0 at ha
        by_contra ha'
        exact ha (by simp [I, chapter08IntervalIndicator, ha'])
      have hcball : c ∈ Metric.ball (0 : ℝ) (b n).rOut := by
        have hc' : c ∈ Function.support ((b n).normed (volume : Measure ℝ)) := by
          simpa [η] using hc
        rw [(b n).support_normed_eq] at hc'
        exact hc'
      rw [Metric.mem_ball, dist_zero_right] at hcball
      have hc' : -(b n).rOut < c ∧ c < (b n).rOut := by
        simpa [abs_lt] using hcball
      have hr := hrout_le n
      constructor <;> linarith [haI.1, haI.2, hc'.1, hc'.2]
    have hAE : ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n => h n x) atTop (𝓝 (I x)) := by
      have hratio : ∀ᶠ n : ℕ in atTop, (b n).rOut ≤ 2 * (b n).rIn := by
        filter_upwards [] with n
        dsimp [b]
        have hn : (0 : ℝ) < n + 1 := by positivity
        field_simp [ne_of_gt hn]
        norm_num
      have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (μ := (volume : Measure ℝ)) (φ := b) (g := I) (l := atTop) (K := (2 : ℝ))
        hb_out hratio hIlocal
      filter_upwards [hconv] with x hx
      have heq : (fun n : ℕ => h n x) =
          (fun n : ℕ => chapter08Convolution (η n) I x) := by
        funext n
        exact hswap n x
      rw [heq]
      exact hx
    let J : Set ℝ := Icc (-3 * T / 4) (3 * T / 4)
    have hJint : Integrable (J.indicator (fun _ : ℝ => (1 : ℝ))) := by
      rw [integrable_indicator_iff]
      · simp [J]
      · exact measurableSet_Icc
    have hGlim : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (G₀ x)) := by
      intro x
      change Tendsto
        (fun n => ∫ y : ℝ, h n y * h n (-(x - y))) atTop
          (𝓝 (∫ y : ℝ, I y * I (-(x - y))))
      apply MeasureTheory.tendsto_integral_of_dominated_convergence
        (J.indicator (fun _ : ℝ => (1 : ℝ)))
      · intro n
        have hc : Continuous (fun y : ℝ => h n (-(x - y))) := by
          apply (hcont n).comp
          fun_prop
        exact ((hcont n).mul hc).measurable.aestronglyMeasurable
      · exact hJint
      · intro n
        filter_upwards [] with y
        have hnon : 0 ≤ h n y * h n (-(x - y)) :=
          mul_nonneg (hnonneg n y) (hnonneg n (-(x - y)))
        rw [Real.norm_eq_abs, abs_of_nonneg hnon]
        by_cases hy : y ∈ J
        · simp only [Set.indicator_of_mem hy]
          calc
            h n y * h n (-(x - y)) ≤ h n y * 1 := by
              exact mul_le_mul_of_nonneg_left (hle n (-(x - y))) (hnonneg n y)
            _ ≤ 1 := by simpa only [mul_one] using hle n y
        · have hzero : h n y = 0 := by
            by_contra hzero
            exact hy (hsupport n hzero)
          simp [Set.indicator_of_notMem hy, hzero]
      · filter_upwards [hAE,
          (quasiMeasurePreserving_sub_left_of_right_invariant
            (volume : Measure ℝ) x).ae hAE] with y hy hyx
        have hyx' : Tendsto (fun n => h n (-(x - y))) atTop
            (𝓝 (I (-(x - y)))) := by
          simpa only [heven_h, hIeven] using hyx
        exact hy.mul hyx'
    have hIintegral : ∫ x : ℝ, I x = T := by
      dsimp [I]
      rw [chapter08IntervalIndicator, integral_indicator measurableSet_Icc]
      rw [setIntegral_const, Real.volume_real_Icc]
      rw [max_eq_left (by linarith)]
      simp
      ring
    have hG₀_zero : G₀ 0 = T := by
      unfold G₀ chapter08Convolution
      calc
        (∫ x : ℝ, I x * I (-(0 - x))) = ∫ x : ℝ, I x := by
          apply integral_congr_ae
          filter_upwards [] with x
          by_cases hx : I x = 0
          · simp [hx]
          · have hx' : I x = 1 := by
              by_cases hxm : x ∈ Icc (-T / 2) (T / 2)
              · simp [I, chapter08IntervalIndicator, hxm]
              · exact (hx (by simp [I, chapter08IntervalIndicator, hxm])).elim
            simp only [zero_sub, neg_neg, hx']
            norm_num
        _ = T := hIintegral
    have hG₀lim : Tendsto (fun n => G n 0) atTop (𝓝 T) := by
      simpa [hG₀_zero] using hGlim 0
    have hG₀lower : ∀ᶠ n : ℕ in atTop, T / 2 < G n 0 := by
      exact hG₀lim (Ioi_mem_nhds (by linarith))
    have hJvolume : ∫ x : ℝ, J.indicator (fun _ : ℝ => (1 : ℝ)) x = 3 * T / 2 := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc]
      rw [max_eq_left (by linarith [hT])]
      ring
    have hGle : ∀ n x, 0 ≤ G n x ∧ G n x ≤ 3 * T / 2 := by
      intro n x
      constructor
      · change 0 ≤ ∫ y : ℝ, h n y * h n (-(x - y))
        apply integral_nonneg
        intro y
        exact mul_nonneg (hnonneg n y) (hnonneg n (-(x - y)))
      · change (∫ y : ℝ, h n y * h n (-(x - y))) ≤ 3 * T / 2
        calc
          (∫ y : ℝ, h n y * h n (-(x - y))) ≤
              ∫ y : ℝ, J.indicator (fun _ : ℝ => (1 : ℝ)) y := by
            apply integral_mono_of_nonneg
            · filter_upwards [] with y
              exact mul_nonneg (hnonneg n y) (hnonneg n (-(x - y)))
            · exact hJint
            · filter_upwards [] with y
              by_cases hy : y ∈ J
              · simp only [Set.indicator_of_mem hy]
                calc
                  h n y * h n (-(x - y)) ≤ h n y * 1 := by
                    exact mul_le_mul_of_nonneg_left (hle n (-(x - y)))
                      (hnonneg n y)
                  _ ≤ 1 := by simpa only [mul_one] using hle n y
              · have hzero : h n y = 0 := by
                  by_contra hzero
                  exact hy (hsupport n hzero)
                simp [Set.indicator_of_notMem hy, hzero]
          _ = 3 * T / 2 := hJvolume
    have hGsupport : ∀ n, Function.support (G n) ⊆ Icc (-3 * T / 2) (3 * T / 2) := by
      intro n x hx
      change chapter08Convolution (h n) (fun y => h n (-y)) x ≠ 0 at hx
      have hxsum : x ∈ Function.support (h n) +
          Function.support (fun y => h n (-y)) := by
        exact (MeasureTheory.support_convolution_subset
          (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℝ))
          (f := h n) (g := fun y => h n (-y))) hx
      rcases hxsum with ⟨a, ha, c, hc, rfl⟩
      have haJ : a ∈ J := hsupport n ha
      have hcJneg : -c ∈ J := by
        change h n (-c) ≠ 0 at hc
        exact hsupport n hc
      have hcJ : c ∈ J := by
        constructor <;> linarith [hcJneg.1, hcJneg.2]
      constructor <;> linarith [haJ.1, haJ.2, hcJ.1, hcJ.2]
    have hQlim : ∀ x, Tendsto (fun n => G n x / G n 0) atTop
        (𝓝 (G₀ x / T)) := by
      intro x
      exact (hGlim x).div hG₀lim (ne_of_gt hT)
    have htri : ∀ x, G₀ x / T = chapter08TriangularAutocorrelation T x := by
      intro x
      have hx := congrFun (chapter08_triangular_is_normalized_autocorrelation hT) x
      change chapter08TriangularAutocorrelation T x = G₀ x / G₀ 0 at hx
      rw [hG₀_zero] at hx
      exact hx.symm
    let Fsm : ℕ → ℝ → ℝ := fun n =>
      chapter08SmoothedUnconditionalTestFunction η T n
    have hFsm_eq : ∀ n x, Fsm n x = G n x / G n 0 / Real.cosh (x / 2) := by
      intro n x
      simp [Fsm, chapter08SmoothedUnconditionalTestFunction,
        chapter08SmoothedUnconditionalTriangle, chapter08NormalizedAutocorrelation,
        G, h]
    have hFpoint : ∀ x, Tendsto (fun n => Fsm n x) atTop
        (𝓝 (chapter08FUnconditionalTriangle T x)) := by
      intro x
      have hq := hQlim x
      have hq' : Tendsto (fun n => G n x / G n 0) atTop
          (𝓝 (chapter08TriangularAutocorrelation T x)) := by
        simpa [htri x] using hq
      have hq'' := hq'.div_const (Real.cosh (x / 2))
      have hleft : (fun n : ℕ => Fsm n x) =
          (fun n : ℕ => G n x / G n 0 / Real.cosh (x / 2)) := by
        funext n
        exact hFsm_eq n x
      rw [hleft]
      simpa [chapter08FUnconditionalTriangle] using hq''
    have hFcont : ∀ n, Continuous (Fsm n) := by
      intro n
      dsimp [Fsm]
      exact (chapter08_smoothed_unconditional_admissible happrox hT hdenom n).1.2.1
    have hKint : Integrable ((Icc (-3 * T / 2) (3 * T / 2)).indicator
        (fun _ : ℝ => (3 : ℝ))) := by
      rw [integrable_indicator_iff]
      · exact integrableOn_const measure_Icc_lt_top.ne
      · exact measurableSet_Icc
    have hIshift_nonneg : ∀ x : ℝ, 0 ≤ x →
        (∫ y : ℝ, |I y - I (y - x)|) ≤ 2 * x := by
      intro x hx
      have hdiff_int : Integrable (fun y : ℝ => |I y - I (y - x)|) := by
        exact (hIint.sub (hIint.comp_sub_right x)).abs
      by_cases hxt : x ≤ T
      · let L : Set ℝ := Icc (-T / 2) (-T / 2 + x)
        let R : Set ℝ := Icc (T / 2) (T / 2 + x)
        have hLint : Integrable (L.indicator (fun _ : ℝ => (1 : ℝ))) := by
          rw [integrable_indicator_iff]
          · simp [L]
          · exact measurableSet_Icc
        have hRint : Integrable (R.indicator (fun _ : ℝ => (1 : ℝ))) := by
          rw [integrable_indicator_iff]
          · simp [R]
          · exact measurableSet_Icc
        have hLvalue : ∫ y : ℝ, L.indicator (fun _ : ℝ => (1 : ℝ)) y = x := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const,
            Real.volume_real_Icc]
          rw [max_eq_left (by linarith)]
          simp
        have hRvalue : ∫ y : ℝ, R.indicator (fun _ : ℝ => (1 : ℝ)) y = x := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const,
            Real.volume_real_Icc]
          rw [max_eq_left (by linarith)]
          simp
        have hpoint : ∀ y : ℝ,
            |I y - I (y - x)| ≤
              L.indicator (fun _ : ℝ => (1 : ℝ)) y +
                R.indicator (fun _ : ℝ => (1 : ℝ)) y := by
          intro y
          have hLnonneg : 0 ≤ L.indicator (fun _ : ℝ => (1 : ℝ)) y := by
            by_cases hy : y ∈ L <;> simp [hy]
          have hRnonneg : 0 ≤ R.indicator (fun _ : ℝ => (1 : ℝ)) y := by
            by_cases hy : y ∈ R <;> simp [hy]
          by_cases hy : y ∈ Icc (-T / 2) (T / 2)
          · by_cases hyx : y - x ∈ Icc (-T / 2) (T / 2)
            · have hIy : I y = 1 := by
                simp [I, chapter08IntervalIndicator, hy]
              have hIyx : I (y - x) = 1 := by
                simp [I, chapter08IntervalIndicator, hyx]
              rw [hIy, hIyx]
              norm_num
              exact add_nonneg hLnonneg hRnonneg
            · have hlow : y - x < -T / 2 := by
                by_contra hlow'
                have hlowle : -T / 2 ≤ y - x := le_of_not_gt hlow'
                have huple : y - x ≤ T / 2 := by linarith [hy.2, hx]
                exact hyx ⟨hlowle, huple⟩
              have hL : y ∈ L := by
                dsimp [L]
                constructor <;> linarith [hy.1, hlow]
              have hIy : I y = 1 := by
                simp [I, chapter08IntervalIndicator, hy]
              have hIyx : I (y - x) = 0 := by
                simp [I, chapter08IntervalIndicator, hyx]
              have hLval : L.indicator (fun _ : ℝ => (1 : ℝ)) y = 1 := by
                simp [hL]
              rw [hIy, hIyx, abs_of_nonneg (by norm_num), hLval]
              linarith
          · by_cases hyx : y - x ∈ Icc (-T / 2) (T / 2)
            · have hlow : -T / 2 ≤ y := by linarith [hyx.1, hx]
              have hhigh : T / 2 < y := by
                by_contra hhigh'
                have hyupper : y ≤ T / 2 := le_of_not_gt hhigh'
                exact hy ⟨hlow, hyupper⟩
              have hR : y ∈ R := by
                dsimp [R]
                constructor <;> linarith [hyx.2]
              have hIy : I y = 0 := by
                simp [I, chapter08IntervalIndicator, hy]
              have hIyx : I (y - x) = 1 := by
                simp [I, chapter08IntervalIndicator, hyx]
              have hRval : R.indicator (fun _ : ℝ => (1 : ℝ)) y = 1 := by
                simp [hR]
              rw [hIy, hIyx, abs_of_nonpos (by norm_num), hRval]
              linarith
            · have hIy : I y = 0 := by
                simp [I, chapter08IntervalIndicator, hy]
              have hIyx : I (y - x) = 0 := by
                simp [I, chapter08IntervalIndicator, hyx]
              simp only [hIy, hIyx, sub_self, abs_zero]
              exact add_nonneg hLnonneg hRnonneg
        have hsumint : Integrable
            (L.indicator (fun _ : ℝ => (1 : ℝ)) +
              R.indicator (fun _ : ℝ => (1 : ℝ))) := hLint.add hRint
        calc
          (∫ y : ℝ, |I y - I (y - x)|) ≤
              ∫ y : ℝ, L.indicator (fun _ : ℝ => (1 : ℝ)) y +
                R.indicator (fun _ : ℝ => (1 : ℝ)) y :=
            integral_mono hdiff_int hsumint hpoint
          _ = x + x := by rw [integral_add hLint hRint, hLvalue, hRvalue]
          _ = 2 * x := by ring
      · have hsumint : Integrable
            (I + (fun y : ℝ => I (y - x))) :=
          hIint.add (hIint.comp_sub_right x)
        have hpoint : ∀ y : ℝ,
            |I y - I (y - x)| ≤ I y + I (y - x) := by
          intro y
          apply (abs_le).2
          constructor <;> linarith [hI_nonneg y, hI_nonneg (y - x)]
        calc
          (∫ y : ℝ, |I y - I (y - x)|) ≤
              ∫ y : ℝ, I y + I (y - x) :=
            integral_mono hdiff_int hsumint hpoint
          _ = T + T := by
            rw [integral_add hIint (hIint.comp_sub_right x), hIintegral,
              integral_sub_right_eq_self, hIintegral]
          _ ≤ 2 * x := by nlinarith
    have hIshift : ∀ x : ℝ,
        (∫ y : ℝ, |I y - I (y - x)|) ≤ 2 * |x| := by
      intro x
      by_cases hx : 0 ≤ x
      · simpa [abs_of_nonneg hx] using hIshift_nonneg x hx
      · have hneg : 0 ≤ -x := by linarith
        have hpos := hIshift_nonneg (-x) hneg
        have heq : (∫ y : ℝ, |I y - I (y - x)|) =
            ∫ y : ℝ, |I y - I (y - (-x))| := by
          calc
            (∫ y : ℝ, |I y - I (y - x)|) =
                ∫ y : ℝ, |I (-y) - I ((-y) - x)| := by
              exact (integral_neg_eq_self
                (fun y : ℝ => |I y - I (y - x)|)
                (volume : Measure ℝ)).symm
            _ = ∫ y : ℝ, |I y - I (y - (-x))| := by
              apply integral_congr_ae
              filter_upwards [] with y
              rw [show (-y) - x = -(y - (-x)) by ring, hIeven y,
                hIeven (y - (-x))]
        rw [heq]
        have hxlt : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hxlt]
        nlinarith [hpos]
    have hImeasurable : Measurable I := by
      dsimp [I]
      exact measurable_const.indicator measurableSet_Icc
    have hImeas : AEStronglyMeasurable I := hImeasurable.aestronglyMeasurable
    have hIbound : ∀ u : ℝ, ‖I u‖ ≤ (1 : ℝ) := by
      intro u
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [hI_nonneg u], hI_le_one u⟩
    have hhcompact : ∀ n, HasCompactSupport (h n) := by
      intro n
      have heq : h n = chapter08Convolution (η n) I := by
        funext x
        exact hswap n x
      rw [heq]
      simpa [chapter08Convolution] using
        (hηcompact n).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hIcompact
    have hhint : ∀ n, Integrable (h n) := by
      intro n
      exact (hcont n).integrable_of_hasCompactSupport (hhcompact n)
    have hconv_shift : ∀ (n : ℕ) (x : ℝ),
        (∫ y : ℝ, |h n y - h n (y - x)|) ≤
          ∫ y : ℝ, |I y - I (y - x)| := by
      intro n x
      let D : ℝ → ℝ := fun u => |I u - I (u - x)|
      have hDint : Integrable D := by
        dsimp [D]
        exact (hIint.sub (hIint.comp_sub_right x)).abs
      have hconvD : Integrable (chapter08Convolution (η n) D) := by
        simpa [chapter08Convolution] using
          (hηint n).integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hDint
      have hpoint : ∀ y : ℝ,
          |h n y - h n (y - x)| ≤ chapter08Convolution (η n) D y := by
        intro y
        have h1 : Integrable (fun z : ℝ => η n z * I (y - z)) := by
          apply (hηint n).mul_bdd
          · exact (hImeasurable.comp (by fun_prop)).aestronglyMeasurable
          · filter_upwards [] with z
            exact hIbound (y - z)
        have h2 : Integrable (fun z : ℝ => η n z * I ((y - x) - z)) := by
          apply (hηint n).mul_bdd
          · exact (hImeasurable.comp (by fun_prop)).aestronglyMeasurable
          · filter_upwards [] with z
            exact hIbound ((y - x) - z)
        have hdiff : Integrable
            (fun z : ℝ => η n z * (I (y - z) - I ((y - x) - z))) := by
          apply (hηint n).mul_bdd
          · exact (hImeasurable.comp (by fun_prop)).aestronglyMeasurable.sub
              (hImeasurable.comp (by fun_prop)).aestronglyMeasurable
          · filter_upwards [] with z
            calc
              ‖I (y - z) - I ((y - x) - z)‖ ≤
                  ‖I (y - z)‖ + ‖I ((y - x) - z)‖ := norm_sub_le _ _
              _ ≤ 2 := by nlinarith [hIbound (y - z), hIbound ((y - x) - z)]
        rw [hswap n y, hswap n (y - x)]
        change
          |(∫ z : ℝ, η n z * I (y - z)) -
              ∫ z : ℝ, η n z * I ((y - x) - z)| ≤
            ∫ z : ℝ, η n z * D (y - z)
        rw [← integral_sub h1 h2]
        calc
          |∫ z : ℝ, η n z * I (y - z) -
              η n z * I ((y - x) - z)| =
              |∫ z : ℝ, η n z * (I (y - z) - I ((y - x) - z))| := by
                congr 1
                apply integral_congr_ae
                filter_upwards [] with z
                ring
          _ =
              ‖∫ z : ℝ, η n z * (I (y - z) - I ((y - x) - z))‖ := by
                rw [Real.norm_eq_abs]
          _ ≤ ∫ z : ℝ,
              ‖η n z * (I (y - z) - I ((y - x) - z))‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
          _ = ∫ z : ℝ, η n z * D (y - z) := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [show (y - x) - z = (y - z) - x by ring]
            simp [D, Real.norm_eq_abs, abs_of_nonneg (hηnonneg n z)]
      have hleft : Integrable (fun y : ℝ => |h n y - h n (y - x)|) := by
        exact ((hhint n).sub ((hhint n).comp_sub_right x)).abs
      calc
        (∫ y : ℝ, |h n y - h n (y - x)|) ≤
            ∫ y : ℝ, chapter08Convolution (η n) D y :=
          integral_mono hleft hconvD hpoint
        _ = (∫ z : ℝ, η n z) * (∫ u : ℝ, D u) := by
          simpa [chapter08Convolution] using
            (MeasureTheory.integral_convolution
              (ContinuousLinearMap.lsmul ℝ ℝ) (hηint n) hDint)
        _ = ∫ u : ℝ, D u := by rw [hηmass n]; simp
        _ = ∫ y : ℝ, |I y - I (y - x)| := by rfl
    have hGdiff_abs : ∀ (n : ℕ) (x : ℝ), |G n 0 - G n x| ≤ 2 * |x| := by
      intro n x
      have hshift : Integrable (fun y : ℝ => h n (y - x)) :=
        (hhint n).comp_sub_right x
      have hself : Integrable (fun y : ℝ => h n y * h n y) := by
        apply (hhint n).mul_bdd
        · exact (hcont n).aestronglyMeasurable
        · filter_upwards [] with y
          rw [Real.norm_eq_abs]
          exact abs_le.2 ⟨by linarith [hnonneg n y], hle n y⟩
      have hcross : Integrable (fun y : ℝ => h n y * h n (y - x)) := by
        apply (hhint n).mul_bdd
        · exact ((hcont n).measurable.comp (by fun_prop)).aestronglyMeasurable
        · filter_upwards [] with y
          rw [Real.norm_eq_abs]
          exact abs_le.2 ⟨by linarith [hnonneg n (y - x)], hle n (y - x)⟩
      have hdiff : Integrable (fun y : ℝ => h n y * (h n y - h n (y - x))) := by
        have htmp : Integrable
            ((fun y : ℝ => h n y * h n y) -
              (fun y : ℝ => h n y * h n (y - x))) := hself.sub hcross
        convert htmp using 1
        funext y
        change h n y * (h n y - h n (y - x)) =
          h n y * h n y - h n y * h n (y - x)
        ring_nf
      have habs : Integrable (fun y : ℝ => |h n y - h n (y - x)|) := by
        exact ((hhint n).sub hshift).abs
      have habsmul : Integrable
          (fun y : ℝ => h n y * |h n y - h n (y - x)|) := by
        have htmp := habs.mul_bdd (hcont n).aestronglyMeasurable (by
          filter_upwards [] with y
          rw [Real.norm_eq_abs]
          exact abs_le.2 ⟨by linarith [hnonneg n y], hle n y⟩)
        simpa [mul_comm] using htmp
      have hGrepr : ∀ z : ℝ,
          G n z = ∫ y : ℝ, h n y * h n (y - z) := by
        intro z
        change (∫ y : ℝ, h n y * h n (-(z - y))) = _
        apply integral_congr_ae
        filter_upwards [] with y
        congr 1
        ring_nf
      have hdiff_integral : G n 0 - G n x =
          ∫ y : ℝ, h n y * (h n y - h n (y - x)) := by
        rw [hGrepr 0, hGrepr x]
        simp only [sub_zero]
        rw [← integral_sub hself hcross]
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      have hpoint : ∀ y : ℝ,
          h n y * |h n y - h n (y - x)| ≤
            |h n y - h n (y - x)| := by
        intro y
        simpa using
          (mul_le_mul_of_nonneg_right (hle n y)
            (abs_nonneg (h n y - h n (y - x))))
      calc
        |G n 0 - G n x| =
            ‖∫ y : ℝ, h n y * (h n y - h n (y - x))‖ := by
          rw [← hdiff_integral, Real.norm_eq_abs]
        _ ≤ ∫ y : ℝ,
            ‖h n y * (h n y - h n (y - x))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
        _ = ∫ y : ℝ, h n y * |h n y - h n (y - x)| := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnonneg n y)]
        _ ≤ ∫ y : ℝ, |h n y - h n (y - x)| :=
          integral_mono habsmul habs hpoint
        _ ≤ 2 * |x| := (hconv_shift n x).trans (hIshift x)
    have hA : Tendsto (fun n => chapter08A (Fsm n)) atTop
        (𝓝 (chapter08A (chapter08FUnconditionalTriangle T))) := by
      have hD := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        ((Icc (-3 * T / 2) (3 * T / 2)).indicator (fun _ : ℝ => (3 : ℝ)))
        (F := fun n x => (Ioi (0 : ℝ)).indicator
          (fun x => Fsm n x * Real.cosh (x / 2)) x)
        (f := fun x => (Ioi (0 : ℝ)).indicator
          (fun x => chapter08FUnconditionalTriangle T x * Real.cosh (x / 2)) x)
        (μ := (volume : Measure ℝ))
        (hF_meas := by
          filter_upwards [] with n
          have hc : Continuous (fun x : ℝ => Real.cosh (x / 2)) := by fun_prop
          exact (((hFcont n).mul hc).measurable.indicator measurableSet_Ioi).aestronglyMeasurable)
        (h_bound := by
          filter_upwards [hG₀lower] with n hn
          filter_upwards [] with x
          by_cases hxK : x ∈ Icc (-3 * T / 2) (3 * T / 2)
          · simp only [Set.indicator_of_mem hxK]
            by_cases hxpos : x ∈ Ioi (0 : ℝ)
            · simp only [Set.indicator_of_mem hxpos]
              have hq : G n x / G n 0 ≤ 3 := by
                apply (div_le_iff₀ (by linarith)).2
                nlinarith [hGle n x |>.2]
              have hqnonneg : 0 ≤ G n x / G n 0 :=
                div_nonneg (hGle n x |>.1) (le_of_lt (by linarith))
              have hprod : 0 ≤ Fsm n x * Real.cosh (x / 2) := by
                rw [hFsm_eq]
                exact mul_nonneg (div_nonneg hqnonneg (Real.cosh_pos _).le)
                  (Real.cosh_pos _).le
              have hprod_eq : Fsm n x * Real.cosh (x / 2) = G n x / G n 0 := by
                rw [hFsm_eq]
                field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
              rw [Real.norm_eq_abs, abs_of_nonneg hprod, hprod_eq]
              exact hq
            · simp [Set.indicator_of_notMem hxpos]
          · simp only [Set.indicator_of_notMem hxK]
            by_cases hxpos : x ∈ Ioi (0 : ℝ)
            · simp only [Set.indicator_of_mem hxpos]
              have hzero : G n x = 0 := by
                by_contra hzero
                exact hxK (hGsupport n hzero)
              have hprod_eq : Fsm n x * Real.cosh (x / 2) = G n x / G n 0 := by
                rw [hFsm_eq]
                field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
              rw [hprod_eq, hzero, zero_div, norm_zero]
            · simp [Set.indicator_of_notMem hxpos])
        (bound_integrable := hKint)
        (h_lim := by
          filter_upwards [] with x
          by_cases hxpos : x ∈ Ioi (0 : ℝ)
          · simp only [Set.indicator_of_mem hxpos]
            exact (hFpoint x).mul_const (Real.cosh (x / 2))
          · simp only [Set.indicator_of_notMem hxpos]
            exact tendsto_const_nhds)
      simpa [chapter08A, integral_indicator measurableSet_Ioi] using hD
    have htriBasic : Chapter08BasicallyAdmissible
        (chapter08FUnconditionalTriangle T) :=
      (chapter08_unconditional_triangle_admissible hT).1
    have hBtarget : IntegrableOn
        (fun x : ℝ => (1 - chapter08FUnconditionalTriangle T x) /
          (2 * Real.sinh (x / 2))) (Ioi 0) :=
      (chapter08_archimedean_integrals_convergent htriBasic).2.1
    have hCtarget :=
      (chapter08_archimedean_integrals_convergent htriBasic).2.2
    have hFdiv : IntegrableOn
        (fun x : ℝ => chapter08FUnconditionalTriangle T x /
          (2 * Real.cosh (x / 2))) (Ioi 0) := by
      have hc : Continuous (fun x : ℝ => chapter08FUnconditionalTriangle T x /
          (2 * Real.cosh (x / 2))) := by
        have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) := by fun_prop
        exact htriBasic.2.1.div hden (fun x => by positivity)
      have hcomp : HasCompactSupport
          (fun x : ℝ => chapter08FUnconditionalTriangle T x /
            (2 * Real.cosh (x / 2))) := by
        have hEq : (fun x : ℝ => chapter08FUnconditionalTriangle T x /
              (2 * Real.cosh (x / 2))) =
            chapter08FUnconditionalTriangle T *
              (fun x => (2 * Real.cosh (x / 2))⁻¹) := by
          funext x
          simp only [Pi.mul_apply, div_eq_mul_inv]
        rw [hEq]
        exact htriBasic.2.2.1.mul_right
      exact (hc.integrable_of_hasCompactSupport hcomp).integrableOn
    have hCbase : IntegrableOn
        (fun x : ℝ => 1 / (2 * Real.cosh (x / 2))) (Ioi 0) := by
      have hs := hCtarget.add hFdiv
      convert hs using 1
      · rfl
      · funext x
        have hden : 2 * Real.cosh (x / 2) ≠ 0 := by positivity
        change 1 / (2 * Real.cosh (x / 2)) =
          (1 - chapter08FUnconditionalTriangle T x) /
              (2 * Real.cosh (x / 2)) +
            chapter08FUnconditionalTriangle T x /
              (2 * Real.cosh (x / 2))
        field_simp [hden]
        ring_nf
    have hCbound : Integrable
        ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => 4 / (2 * Real.cosh (x / 2)))) := by
      rw [integrable_indicator_iff]
      · change Integrable (fun x : ℝ => 4 / (2 * Real.cosh (x / 2)))
          (volume.restrict (Ioi 0))
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          hCbase.const_mul (4 : ℝ)
      · exact measurableSet_Ioi
    have hC : Tendsto (fun n => chapter08C (Fsm n)) atTop
        (𝓝 (chapter08C (chapter08FUnconditionalTriangle T))) := by
      have hD := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => 4 / (2 * Real.cosh (x / 2))))
        (F := fun n x => (Ioi (0 : ℝ)).indicator
          (fun x => (1 - Fsm n x) / (2 * Real.cosh (x / 2))) x)
        (f := fun x => (Ioi (0 : ℝ)).indicator
          (fun x => (1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.cosh (x / 2))) x)
        (μ := (volume : Measure ℝ))
        (hF_meas := by
          filter_upwards [] with n
          have hc : Continuous (fun x : ℝ =>
              (1 - Fsm n x) / (2 * Real.cosh (x / 2))) := by
            have hnum : Continuous (fun x : ℝ => 1 - Fsm n x) :=
              continuous_const.sub (hFcont n)
            have hden : Continuous (fun x : ℝ => 2 * Real.cosh (x / 2)) := by
              fun_prop
            exact hnum.div hden (fun x => by positivity)
          exact (hc.measurable.indicator measurableSet_Ioi).aestronglyMeasurable)
        (h_bound := by
          filter_upwards [hG₀lower] with n hn
          filter_upwards [] with x
          by_cases hxpos : x ∈ Ioi (0 : ℝ)
          · simp only [Set.indicator_of_mem hxpos]
            have hq : G n x / G n 0 ≤ 3 := by
              apply (div_le_iff₀ (by linarith)).2
              nlinarith [hGle n x |>.2]
            have hqnonneg : 0 ≤ G n x / G n 0 :=
              div_nonneg (hGle n x |>.1) (le_of_lt (by linarith))
            have hFnonneg : 0 ≤ Fsm n x := by
              rw [hFsm_eq]
              exact div_nonneg hqnonneg (Real.cosh_pos _).le
            have hFle : Fsm n x ≤ 3 := by
              rw [hFsm_eq]
              apply (div_le_iff₀ (Real.cosh_pos _)).2
              nlinarith [hq, Real.one_le_cosh (x / 2)]
            have hnum : |1 - Fsm n x| ≤ 4 := by
              apply (abs_le).2
              constructor <;> nlinarith
            have hden : 0 < 2 * Real.cosh (x / 2) := by positivity
            rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
            exact (div_le_div_iff_of_pos_right hden).2 hnum
          · simp [Set.indicator_of_notMem hxpos])
        (bound_integrable := hCbound)
        (h_lim := by
          filter_upwards [] with x
          by_cases hxpos : x ∈ Ioi (0 : ℝ)
          · simp only [Set.indicator_of_mem hxpos]
            have hden : 2 * Real.cosh (x / 2) ≠ 0 := by positivity
            exact (tendsto_const_nhds.sub (hFpoint x)).div_const
              (2 * Real.cosh (x / 2))
          · simp only [Set.indicator_of_notMem hxpos]
            exact tendsto_const_nhds)
      simpa [chapter08C, integral_indicator measurableSet_Ioi] using hD
    have hBbound : Integrable
        ((Ioi (0 : ℝ)).indicator
          (fun x => 20 * ((1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.sinh (x / 2))))) := by
      rw [integrable_indicator_iff]
      · change Integrable
          (fun x => 20 * ((1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.sinh (x / 2)))) (volume.restrict (Ioi 0))
        simpa [mul_comm, mul_left_comm, mul_assoc] using hBtarget.const_mul (20 : ℝ)
      · exact measurableSet_Ioi
    have hB : Tendsto (fun n => chapter08B (Fsm n)) atTop
        (𝓝 (chapter08B (chapter08FUnconditionalTriangle T))) := by
      have hD := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        ((Ioi (0 : ℝ)).indicator
          (fun x => 20 * ((1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.sinh (x / 2)))))
        (F := fun n x => (Ioi (0 : ℝ)).indicator
          (fun x => (1 - Fsm n x) / (2 * Real.sinh (x / 2))) x)
        (f := fun x => (Ioi (0 : ℝ)).indicator
          (fun x => (1 - chapter08FUnconditionalTriangle T x) /
            (2 * Real.sinh (x / 2))) x)
        (μ := (volume : Measure ℝ))
        (hF_meas := by
          filter_upwards [] with n
          exact (((measurable_const.sub (hFcont n).measurable).div
            (measurable_const.mul
              (Real.continuous_sinh.measurable.comp
                (measurable_id.div measurable_const)))).indicator
            measurableSet_Ioi).aestronglyMeasurable)
        (h_bound := by
          filter_upwards [hG₀lower] with n hn
          filter_upwards [] with x
          by_cases hxpos : x ∈ Ioi (0 : ℝ)
          · simp only [Set.indicator_of_mem hxpos]
            have hx : 0 < x := hxpos
            have hG0pos : 0 < G n 0 := lt_trans (by positivity) hn
            have hq : G n x / G n 0 ≤ 3 := by
              apply (div_le_iff₀ hG0pos).2
              nlinarith only [hGle n x |>.2, hn]
            have hqnonneg : 0 ≤ G n x / G n 0 :=
              div_nonneg (hGle n x |>.1) hG0pos.le
            have hqdiff : |1 - G n x / G n 0| ≤ 4 * x / T := by
              have hdiff := hGdiff_abs n x
              rw [abs_of_pos hx] at hdiff
              have hqeq : |1 - G n x / G n 0| =
                  |G n 0 - G n x| / G n 0 := by
                have hqeq' : 1 - G n x / G n 0 =
                    (G n 0 - G n x) / G n 0 := by
                  field_simp [ne_of_gt hG0pos]
                rw [hqeq', abs_div, abs_of_pos hG0pos]
              rw [hqeq]
              apply (div_le_iff₀ hG0pos).2
              calc
                |G n 0 - G n x| ≤ 2 * x := hdiff
                _ ≤ (4 * x / T) * G n 0 := by
                  have hmul := mul_le_mul_of_nonneg_left
                    (show T / 2 ≤ G n 0 by linarith only [hn])
                    (show 0 ≤ 4 * x / T by positivity)
                  calc
                    2 * x = (4 * x / T) * (T / 2) := by
                      field_simp [ne_of_gt hT]
                      ring
                    _ ≤ (4 * x / T) * G n 0 := hmul
            have hcpos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
            have hcinvnonneg : 0 ≤ (Real.cosh (x / 2))⁻¹ :=
              inv_nonneg.mpr hcpos.le
            have hcinvle : (Real.cosh (x / 2))⁻¹ ≤ 1 :=
              (inv_le_one₀ hcpos).2 (Real.one_le_cosh _)
            have hcorr : 0 ≤ 1 - (Real.cosh (x / 2))⁻¹ :=
              sub_nonneg.mpr hcinvle
            have hcorrle : 1 - (Real.cosh (x / 2))⁻¹ ≤ 1 := by
              linarith only [hcinvnonneg]
            have htri_nonneg : 0 ≤ chapter08TriangularAutocorrelation T x :=
              le_max_right _ _
            have htri_le_one : chapter08TriangularAutocorrelation T x ≤ 1 := by
              unfold chapter08TriangularAutocorrelation
              apply max_le
              · have habs : 0 ≤ |x| / T := div_nonneg (abs_nonneg _) hT.le
                linarith only [habs]
              · norm_num
            have htri_div : chapter08TriangularAutocorrelation T x /
                Real.cosh (x / 2) ≤ chapter08TriangularAutocorrelation T x := by
              rw [div_eq_mul_inv]
              calc
                chapter08TriangularAutocorrelation T x * (Real.cosh (x / 2))⁻¹ ≤
                    chapter08TriangularAutocorrelation T x * 1 :=
                  mul_le_mul_of_nonneg_left hcinvle htri_nonneg
                _ = chapter08TriangularAutocorrelation T x := by ring
            have hNge : 1 - chapter08TriangularAutocorrelation T x ≤
                1 - chapter08FUnconditionalTriangle T x := by
              rw [chapter08FUnconditionalTriangle]
              exact sub_le_sub_left htri_div 1
            have hNdecomp : 1 - chapter08FUnconditionalTriangle T x =
                (1 - chapter08TriangularAutocorrelation T x) +
                  chapter08TriangularAutocorrelation T x *
                    (1 - (Real.cosh (x / 2))⁻¹) := by
              rw [chapter08FUnconditionalTriangle]
              simp only [div_eq_mul_inv]
              ring
            have hdecomp : 1 - Fsm n x =
                (1 - G n x / G n 0) +
                  (G n x / G n 0) * (1 - (Real.cosh (x / 2))⁻¹) := by
              rw [hFsm_eq]
              simp only [div_eq_mul_inv]
              ring
            have hnum : |1 - Fsm n x| ≤
                4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) := by
              rw [hdecomp]
              calc
                |(1 - G n x / G n 0) +
                    (G n x / G n 0) * (1 - (Real.cosh (x / 2))⁻¹)| ≤
                    |1 - G n x / G n 0| +
                      |(G n x / G n 0) * (1 - (Real.cosh (x / 2))⁻¹)| :=
                  abs_add_le _ _
                _ = |1 - G n x / G n 0| +
                    (G n x / G n 0) * (1 - (Real.cosh (x / 2))⁻¹) := by
                  rw [abs_mul, abs_of_nonneg hqnonneg, abs_of_nonneg hcorr]
                _ ≤ 4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) := by
                  gcongr
            have hnumcomp : |1 - Fsm n x| ≤
                20 * (1 - chapter08FUnconditionalTriangle T x) := by
              by_cases hsmall : x ≤ T / 2
              · have hxratio : x / T ≤ (1 : ℝ) / 2 := by
                  apply (div_le_iff₀ hT).2
                  linarith only [hsmall, hT]
                have htrieq : chapter08TriangularAutocorrelation T x = 1 - x / T := by
                  have hnon : 0 ≤ 1 - x / T := by
                    apply sub_nonneg.mpr
                    apply (div_le_iff₀ hT).2
                    linarith only [hsmall, hT]
                  simp [chapter08TriangularAutocorrelation, abs_of_pos hx,
                    max_eq_left hnon]
                have hNx : x / T ≤ 1 - chapter08FUnconditionalTriangle T x := by
                  rw [htrieq] at hNge
                  linarith only [hNge]
                have htrihalf : (1 : ℝ) / 2 ≤
                    chapter08TriangularAutocorrelation T x := by
                  rw [htrieq]
                  linarith only [hxratio]
                have hcorrhalf : (1 - (Real.cosh (x / 2))⁻¹) / 2 ≤
                    1 - chapter08FUnconditionalTriangle T x := by
                  rw [hNdecomp]
                  have hmul :
                      (1 - (Real.cosh (x / 2))⁻¹) / 2 ≤
                        chapter08TriangularAutocorrelation T x *
                          (1 - (Real.cosh (x / 2))⁻¹) := by
                    calc
                      (1 - (Real.cosh (x / 2))⁻¹) / 2 =
                          ((1 : ℝ) / 2) * (1 - (Real.cosh (x / 2))⁻¹) := by ring
                      _ ≤ chapter08TriangularAutocorrelation T x *
                          (1 - (Real.cosh (x / 2))⁻¹) :=
                        mul_le_mul_of_nonneg_right htrihalf hcorr
                  calc
                    (1 - (Real.cosh (x / 2))⁻¹) / 2 ≤
                        chapter08TriangularAutocorrelation T x *
                          (1 - (Real.cosh (x / 2))⁻¹) := hmul
                    _ ≤ (1 - chapter08TriangularAutocorrelation T x) +
                        chapter08TriangularAutocorrelation T x *
                          (1 - (Real.cosh (x / 2))⁻¹) :=
                      le_add_of_nonneg_left (sub_nonneg.mpr htri_le_one)
                have hNnonneg : 0 ≤ 1 - chapter08FUnconditionalTriangle T x := by
                  exact (sub_nonneg.mpr htri_le_one).trans hNge
                calc
                  |1 - Fsm n x| ≤
                      4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) := hnum
                  _ ≤ 20 * (1 - chapter08FUnconditionalTriangle T x) := by
                    have hxa : 4 * x / T ≤
                        4 * (1 - chapter08FUnconditionalTriangle T x) := by
                      simpa [div_eq_mul_inv, mul_assoc] using
                        (mul_le_mul_of_nonneg_left hNx
                          (by norm_num : (0 : ℝ) ≤ 4))
                    have hcc : 3 * (1 - (Real.cosh (x / 2))⁻¹) ≤
                        6 * (1 - chapter08FUnconditionalTriangle T x) := by
                      calc
                        3 * (1 - (Real.cosh (x / 2))⁻¹) =
                            6 * ((1 - (Real.cosh (x / 2))⁻¹) / 2) := by ring
                        _ ≤ 6 * (1 - chapter08FUnconditionalTriangle T x) :=
                          mul_le_mul_of_nonneg_left hcorrhalf (by norm_num : (0 : ℝ) ≤ 6)
                    calc
                      4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) ≤
                          4 * (1 - chapter08FUnconditionalTriangle T x) +
                            6 * (1 - chapter08FUnconditionalTriangle T x) :=
                        add_le_add hxa hcc
                      _ = 10 * (1 - chapter08FUnconditionalTriangle T x) := by ring
                      _ ≤ 20 * (1 - chapter08FUnconditionalTriangle T x) := by
                        exact mul_le_mul_of_nonneg_right
                          (by norm_num : (10 : ℝ) ≤ 20) hNnonneg
              · have hmid : T / 2 < x := not_le.mp hsmall
                by_cases hlarge : x ≤ 3 * T / 2
                · have hxratio : x / T ≤ (3 : ℝ) / 2 := by
                    apply (div_le_iff₀ hT).2
                    linarith only [hlarge]
                  have htrihalf :
                      chapter08TriangularAutocorrelation T x ≤ (1 : ℝ) / 2 := by
                    unfold chapter08TriangularAutocorrelation
                    apply max_le
                    · rw [abs_of_pos hx]
                      have hdiv : (1 : ℝ) / 2 ≤ x / T := by
                        apply (le_div_iff₀ hT).2
                        linarith only [hmid]
                      linarith only [hdiv]
                    · norm_num
                  have hNhalf : (1 : ℝ) / 2 ≤
                      1 - chapter08FUnconditionalTriangle T x := by
                    have hbase : (1 : ℝ) / 2 ≤
                        1 - chapter08TriangularAutocorrelation T x := by
                      calc
                        (1 : ℝ) / 2 = 1 - (1 : ℝ) / 2 := by ring
                        _ ≤ 1 - chapter08TriangularAutocorrelation T x :=
                          sub_le_sub_left htrihalf 1
                    exact hbase.trans hNge
                  have hNnonneg : 0 ≤ 1 - chapter08FUnconditionalTriangle T x :=
                    (show 0 ≤ (1 : ℝ) / 2 by norm_num).trans hNhalf
                  calc
                    |1 - Fsm n x| ≤
                        4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) := hnum
                    _ ≤ 20 * (1 - chapter08FUnconditionalTriangle T x) := by
                      have hxa : 4 * x / T ≤ (6 : ℝ) := by
                        calc
                          4 * x / T ≤ 4 * ((3 : ℝ) / 2) :=
                            by
                              simpa [div_eq_mul_inv, mul_assoc] using
                                (mul_le_mul_of_nonneg_left hxratio
                                  (by norm_num : (0 : ℝ) ≤ 4))
                          _ = 6 := by norm_num
                      have hcc : 3 * (1 - (Real.cosh (x / 2))⁻¹) ≤ (3 : ℝ) := by
                        calc
                          3 * (1 - (Real.cosh (x / 2))⁻¹) ≤ 3 * 1 :=
                            mul_le_mul_of_nonneg_left hcorrle
                              (by norm_num : (0 : ℝ) ≤ 3)
                          _ = 3 := by ring
                      calc
                        4 * x / T + 3 * (1 - (Real.cosh (x / 2))⁻¹) ≤
                            (9 : ℝ) := by
                              exact (add_le_add hxa hcc).trans_eq (by ring)
                        _ ≤ 18 * (1 - chapter08FUnconditionalTriangle T x) := by
                          have hmul := mul_le_mul_of_nonneg_right hNhalf
                            (by norm_num : (0 : ℝ) ≤ 18)
                          calc
                            (9 : ℝ) = 18 * ((1 : ℝ) / 2) := by ring
                            _ = ((1 : ℝ) / 2) * 18 := by ring
                            _ ≤ (1 - chapter08FUnconditionalTriangle T x) * 18 := hmul
                            _ = 18 * (1 - chapter08FUnconditionalTriangle T x) := by ring
                        _ ≤ 20 * (1 - chapter08FUnconditionalTriangle T x) :=
                          mul_le_mul_of_nonneg_right
                            (by norm_num : (18 : ℝ) ≤ 20) hNnonneg
                · have hlarge' : 3 * T / 2 < x := lt_of_not_ge hlarge
                  have hzero : G n x = 0 := by
                    by_contra hzero
                    exact (not_lt_of_ge (hGsupport n hzero).2) hlarge'
                  have hFzero : Fsm n x = 0 := by
                    rw [hFsm_eq, hzero]
                    simp
                  have htrizero : chapter08TriangularAutocorrelation T x = 0 := by
                    have hneg : 1 - x / T ≤ 0 := by
                      apply sub_nonpos.mpr
                      apply (le_div_iff₀ hT).2
                      have hTle : T ≤ x := by linarith only [hlarge', hT]
                      simpa only [one_mul] using hTle
                    simp [chapter08TriangularAutocorrelation, abs_of_pos hx,
                      max_eq_right hneg]
                  have htargetzero : chapter08FUnconditionalTriangle T x = 0 := by
                    simp [chapter08FUnconditionalTriangle, htrizero]
                  rw [hFzero, htargetzero]
                  norm_num
            have hden : 0 < 2 * Real.sinh (x / 2) := by positivity
            rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
            calc
              |1 - Fsm n x| / (2 * Real.sinh (x / 2)) ≤
                  (20 * (1 - chapter08FUnconditionalTriangle T x)) /
                    (2 * Real.sinh (x / 2)) :=
                (div_le_div_iff_of_pos_right hden).2 hnumcomp
              _ = 20 * ((1 - chapter08FUnconditionalTriangle T x) /
                    (2 * Real.sinh (x / 2))) := by ring
          · simp [Set.indicator_of_notMem hxpos])
        (bound_integrable := hBbound)
        (h_lim := by
          filter_upwards [] with x
          by_cases hxpos : x ∈ Ioi (0 : ℝ)
          · simp only [Set.indicator_of_mem hxpos]
            exact (tendsto_const_nhds.sub (hFpoint x)).div_const
              (2 * Real.sinh (x / 2))
          · simp only [Set.indicator_of_notMem hxpos]
            exact tendsto_const_nhds)
      simpa [chapter08B, integral_indicator measurableSet_Ioi] using hD
    exact And.intro hA (And.intro hB hC)

theorem chapter08_unconditional_triangle_near_zero
    {T : ℝ} (hT : 0 < T) :
    (fun x : ℝ =>
        1 - chapter08FUnconditionalTriangle T x - x / T) =O[nhdsWithin 0 (Ici 0)]
      (fun x : ℝ => x ^ 2) := by
  let l : Filter ℝ := nhdsWithin 0 (Ici 0)
  have hscale : Tendsto (fun x : ℝ => x / 4) l (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    simpa [l] using (h0.div_const (4 : ℝ)).mono_left nhdsWithin_le_nhds
  have hs : (fun x : ℝ => Real.sinh (x / 4)) =O[l] (fun x => x) := by
    have hright : (fun x : ℝ => x / 4) =O[l] (fun x => x) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (Asymptotics.isBigO_const_mul_self (1 / 4 : ℝ) (fun x : ℝ => x) l)
    simpa [Function.comp_def] using
      (Real.isEquivalent_sinh.isBigO.comp_tendsto hscale).trans hright
  have hs2 : (fun x : ℝ => Real.sinh (x / 4) ^ 2) =O[l]
      (fun x => x ^ 2) := by
    simpa [pow_two] using hs.mul hs
  have hcosh_inv : (fun x : ℝ => (Real.cosh (x / 2))⁻¹) =O[l]
      (fun _ : ℝ => (1 : ℝ)) := by
    have hc : Continuous (fun x : ℝ => (Real.cosh (x / 2))⁻¹) :=
      (Real.continuous_cosh.comp (continuous_id.div_const 2)).inv₀
        (fun x => ne_of_gt (Real.cosh_pos (x / 2)))
    exact hc.continuousAt.isBigO.mono nhdsWithin_le_nhds
  have hleft : (fun x : ℝ => 1 - x / T) =O[l]
      (fun _ : ℝ => (1 : ℝ)) := by
    apply (continuous_const.sub (continuous_id.div_const T)).continuousAt.isBigO.mono
      nhdsWithin_le_nhds
  have hbase : (fun x : ℝ =>
      Real.sinh (x / 4) ^ 2 * (Real.cosh (x / 2))⁻¹) =O[l]
      (fun x => x ^ 2) := by
    simpa [mul_one] using hs2.mul hcosh_inv
  have htwice : (fun x : ℝ =>
      2 * (Real.sinh (x / 4) ^ 2 * (Real.cosh (x / 2))⁻¹)) =O[l]
      (fun x => x ^ 2) := by
    exact (Asymptotics.isBigO_const_mul_self 2
      (fun x : ℝ => Real.sinh (x / 4) ^ 2 * (Real.cosh (x / 2))⁻¹) l).trans hbase
  have hprod : (fun x : ℝ =>
      (1 - x / T) *
        (2 * (Real.sinh (x / 4) ^ 2 * (Real.cosh (x / 2))⁻¹))) =O[l]
      (fun x => x ^ 2) := by
    simpa [mul_one] using hleft.mul htwice
  have hmem : ∀ᶠ x : ℝ in l, x ∈ Set.Icc 0 T := by
    have hIio : Iio T ∈ l := by
      exact (show nhdsWithin 0 (Ici (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
        (Iio_mem_nhds hT)
    have hset : Iio T ∩ Ici (0 : ℝ) ∈ l := by
      exact inter_mem hIio self_mem_nhdsWithin
    filter_upwards [hset] with x hx
    exact ⟨hx.2, le_of_lt hx.1⟩
  have heq : (fun x : ℝ =>
      (1 - x / T) *
        (2 * (Real.sinh (x / 4) ^ 2 * (Real.cosh (x / 2))⁻¹))) =ᶠ[l]
      (fun x : ℝ => 1 - chapter08FUnconditionalTriangle T x - x / T) := by
    filter_upwards [hmem] with x hx
    have hx0 : 0 ≤ x := hx.1
    have hxT : x ≤ T := hx.2
    have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
    have hlin : 0 ≤ 1 - x / T := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hT).2 (by simpa using hxT)
    rw [chapter08FUnconditionalTriangle, chapter08TriangularAutocorrelation,
      hratio, max_eq_left hlin]
    have hcosh : Real.cosh (x / 2) =
        1 + 2 * Real.sinh (x / 4) ^ 2 := by
      have h1 := Real.cosh_two_mul (x / 4)
      have h2 := Real.cosh_sq_sub_sinh_sq (x / 4)
      convert h1 using 1
      all_goals ring_nf at *
      all_goals nlinarith
    field_simp [ne_of_gt (Real.cosh_pos (x / 2))]
    rw [hcosh]
    ring
  exact hprod.congr' heq (Eventually.of_forall (fun x => rfl))

theorem chapter08_unconditional_triangle_B_integrand_tendsto
    {T : ℝ} (hT : 0 < T) :
    Tendsto
      (fun x : ℝ =>
        (1 - chapter08FUnconditionalTriangle T x) / (2 * Real.sinh (x / 2)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (1 / T)) := by
  let l : Filter ℝ := nhdsWithin 0 (Ici 0)
  let lp : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hlittle : (fun x : ℝ => x ^ 2) =o[l] (fun x : ℝ => x) := by
    exact (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num)).mono
      nhdsWithin_le_nhds
  have hrem : (fun x : ℝ =>
      1 - chapter08FUnconditionalTriangle T x - x / T) =o[l]
      (fun x : ℝ => x) := by
    exact (chapter08_unconditional_triangle_near_zero hT).trans_isLittleO hlittle
  have hremdiv : Tendsto (fun x : ℝ =>
      (1 - chapter08FUnconditionalTriangle T x - x / T) / x) lp (𝓝 0) := by
    have h := hrem.tendsto_div_nhds_zero
    exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hscale : Tendsto (fun x : ℝ => x / 2) lp (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    simpa [lp] using (h0.div_const (2 : ℝ)).mono_left nhdsWithin_le_nhds
  have hs : (fun x : ℝ => Real.sinh (x / 2)) ~[lp]
      (fun x : ℝ => x / 2) := by
    simpa [Function.comp_def] using Real.isEquivalent_sinh.comp_tendsto hscale
  have hdeneq : (fun x : ℝ => 2 * Real.sinh (x / 2)) ~[lp]
      (fun x : ℝ => x) := by
    have hc : (fun _ : ℝ => (2 : ℝ)) ~[lp] (fun _ : ℝ => (2 : ℝ)) :=
      Asymptotics.IsEquivalent.refl
    convert hc.mul hs using 1
    · funext x
      simp only [Pi.mul_apply]
    · funext x
      simp only [Pi.mul_apply]
      ring
  have hdenpos : ∀ᶠ x : ℝ in lp, 2 * Real.sinh (x / 2) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ne_of_gt (mul_pos (by norm_num)
      (Real.sinh_pos_iff.mpr (div_pos hx (by norm_num))))
  have hden : Tendsto (fun x : ℝ => x / (2 * Real.sinh (x / 2))) lp (𝓝 1) := by
    exact (Asymptotics.isEquivalent_iff_tendsto_one hdenpos).mp hdeneq.symm
  have hmain : Tendsto (fun x : ℝ =>
      (x / T) / (2 * Real.sinh (x / 2))) lp (𝓝 (1 / T)) := by
    have h := hden.const_mul (1 / T)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hremprod : Tendsto (fun x : ℝ =>
      (1 - chapter08FUnconditionalTriangle T x - x / T) /
        (2 * Real.sinh (x / 2))) lp (𝓝 0) := by
    have h := hremdiv.mul hden
    have h' : Tendsto (fun x : ℝ =>
        (1 - chapter08FUnconditionalTriangle T x - x / T) / x *
          (x / (2 * Real.sinh (x / 2)))) lp (𝓝 0) := by
      simpa using h
    convert h' using 1
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
  have hsum := hmain.add hremprod
  have hsum' : Tendsto (fun x : ℝ =>
      x / T / (2 * Real.sinh (x / 2)) +
        (1 - chapter08FUnconditionalTriangle T x - x / T) /
          (2 * Real.sinh (x / 2))) lp (𝓝 (1 / T)) := by
    simpa using hsum
  convert hsum' using 1
  funext x
  ring

theorem chapter08_dominated_convergence_transfers_lower_bound
    {K : Type*} [Field K] [NumberField K]
    (hK : 0 < Chapter08Degree K) {F : ℝ → ℝ} (u : ℕ → ℝ → ℝ)
    (hbound : ∀ n,
      Real.log (Chapter08RootDiscriminant K) ≥
        Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
          chapter08SignatureProportion K * (Real.pi / 2) -
          4 * chapter08A (u n) / (Chapter08Degree K : ℝ) -
          chapter08B (u n) -
          chapter08SignatureProportion K * chapter08C (u n))
    (hA : Tendsto (fun n => chapter08A (u n)) atTop (𝓝 (chapter08A F)))
    (hB : Tendsto (fun n => chapter08B (u n)) atTop (𝓝 (chapter08B F)))
    (hC : Tendsto (fun n => chapter08C (u n)) atTop (𝓝 (chapter08C F))) :
    Real.log (Chapter08RootDiscriminant K) ≥
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        chapter08SignatureProportion K * (Real.pi / 2) -
        4 * chapter08A F / (Chapter08Degree K : ℝ) -
        chapter08B F -
        chapter08SignatureProportion K * chapter08C F := by
  have hd : (Chapter08Degree K : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hK)
  have hA' : Tendsto (fun n => 4 * chapter08A (u n) /
      (Chapter08Degree K : ℝ)) atTop
      (𝓝 (4 * chapter08A F / (Chapter08Degree K : ℝ))) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hd] using
      hA.const_mul (4 / (Chapter08Degree K : ℝ))
  have hC' : Tendsto (fun n => chapter08SignatureProportion K * chapter08C (u n))
      atTop (𝓝 (chapter08SignatureProportion K * chapter08C F)) :=
    hC.const_mul _
  have hlim : Tendsto
      (fun n =>
        Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
          chapter08SignatureProportion K * (Real.pi / 2) -
          4 * chapter08A (u n) / (Chapter08Degree K : ℝ) -
          chapter08B (u n) -
          chapter08SignatureProportion K * chapter08C (u n))
      atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
        chapter08SignatureProportion K * (Real.pi / 2) -
        4 * chapter08A F / (Chapter08Degree K : ℝ) -
        chapter08B F -
        chapter08SignatureProportion K * chapter08C F)) := by
    have h0 :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ =>
          Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
            chapter08SignatureProportion K * (Real.pi / 2)) atTop
          (𝓝 (Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
            chapter08SignatureProportion K * (Real.pi / 2)))).sub hA'
    have h1 := h0.sub hB
    have h2 := h1.sub hC'
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2
  apply (le_of_tendsto hlim)
  exact Eventually.of_forall (fun n => hbound n)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
