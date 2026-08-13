import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08.Dependencies
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08

open MeasureTheory Set

noncomputable section

/-! ## 8.2 The triangular autocorrelation -/

noncomputable def chapter08Convolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

def chapter08NormalizedAutocorrelation (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  let G := chapter08Convolution h (fun y => h (-y))
  G x / G 0

def chapter08Sinc (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.sin u / u

/-!
The source fixes `T > 0` before introducing the triangular family and explicitly takes the tail
index `m` in `ℕ` (including `m = 0`).  The declarations retain those local conventions as
hypotheses where they are needed for total Lean statements.
-/

def chapter08IntervalIndicator (T : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc (-T / 2) (T / 2)) (fun _ => 1)

def chapter08TriangularAutocorrelation (T : ℝ) (x : ℝ) : ℝ :=
  max (1 - |x| / T) 0

def chapter08FUnconditionalTriangle (T : ℝ) : ℝ → ℝ :=
  fun x => chapter08TriangularAutocorrelation T x / Real.cosh (x / 2)

def chapter08FGRHTriangle (T : ℝ) : ℝ → ℝ :=
  chapter08TriangularAutocorrelation T

theorem chapter08_normalized_autocorrelation_zero
    {h : ℝ → ℝ}
    (h0 : chapter08Convolution h (fun y => h (-y)) 0 ≠ 0) :
    chapter08NormalizedAutocorrelation h 0 = 1 := by
  simp [chapter08NormalizedAutocorrelation, h0]

theorem chapter08_sinc_zero :
    chapter08Sinc 0 = 1 := by
  simp [chapter08Sinc]

theorem chapter08_triangular_even {T : ℝ} :
    Chapter08Even (chapter08TriangularAutocorrelation T) := by
  intro x
  simp [chapter08TriangularAutocorrelation, abs_neg]

theorem chapter08_triangular_zero {T : ℝ} (hT : 0 < T) :
    chapter08TriangularAutocorrelation T 0 = 1 := by
  unfold chapter08TriangularAutocorrelation
  rw [max_eq_left]
  · simp
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hT).2
    simpa using hT.le

theorem chapter08_interval_indicator_even {T : ℝ} (hT : 0 < T) :
    Chapter08Even (chapter08IntervalIndicator T) := by
  intro x
  have hTabs : |T| = T := abs_of_nonneg hT.le
  have hmem' : x ∈ Set.Icc (-|T| / 2) (|T| / 2) ↔
      -x ∈ Set.Icc (-|T| / 2) (|T| / 2) := by
    constructor <;> intro hx
    · constructor <;> linarith [hx.1, hx.2]
    · constructor <;> linarith [hx.1, hx.2]
  have hmem : x ∈ Set.Icc (-T / 2) (T / 2) ↔
      -x ∈ Set.Icc (-T / 2) (T / 2) := by
    simpa [hTabs] using hmem'
  by_cases hx : x ∈ Set.Icc (-T / 2) (T / 2)
  · simp [chapter08IntervalIndicator, hx, hmem.mp hx]
  · simp [chapter08IntervalIndicator, hx, hmem.not.mp hx]

theorem chapter08_triangular_is_normalized_autocorrelation
    {T : ℝ} (hT : 0 < T) :
    chapter08TriangularAutocorrelation T =
      chapter08NormalizedAutocorrelation (chapter08IntervalIndicator T) := by
  let A : Set ℝ := Set.Icc (-T / 2) (T / 2)
  have hconv : ∀ x : ℝ,
      chapter08Convolution (chapter08IntervalIndicator T)
          (fun y => chapter08IntervalIndicator T (-y)) x =
        (volume : Measure ℝ).real
          (A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A) := by
    intro x
    unfold chapter08Convolution
    change (∫ t : ℝ,
        (A.indicator (fun _ : ℝ => (1 : ℝ)) t) *
          (A.indicator (fun _ : ℝ => (1 : ℝ)) (-(x - t)))) = _
    have hmeas : MeasurableSet
        (A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A) := by
      apply measurableSet_Icc.inter
      exact measurableSet_Icc.preimage (by fun_prop)
    apply (integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))).trans
    · rw [integral_indicator_one hmeas]
    by_cases ht : t ∈ A
    · by_cases htx : -(x - t) ∈ A
      · have hmem : t ∈ A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A := ⟨ht, htx⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem htx,
          Set.indicator_of_mem hmem]
        simp
      · have hnot : t ∉ A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A := by
          intro h
          exact htx h.2
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem htx,
          Set.indicator_of_notMem hnot]
        simp
    · have hnot : t ∉ A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A := by
        intro h
        exact ht h.1
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hnot]
      simp
  funext x
  dsimp [chapter08NormalizedAutocorrelation]
  have hset (x : ℝ) :
      A ∩ (fun t : ℝ => -(x - t)) ⁻¹' A =
        Set.Icc (max (-T / 2) (x - T / 2))
          (min (T / 2) (x + T / 2)) := by
    ext t
    constructor
    · rintro ⟨htA, htB⟩
      change -T / 2 ≤ t ∧ t ≤ T / 2 at htA
      change -T / 2 ≤ -(x - t) ∧ -(x - t) ≤ T / 2 at htB
      change max (-T / 2) (x - T / 2) ≤ t ∧
        t ≤ min (T / 2) (x + T / 2)
      constructor
      · exact max_le htA.1 (by linarith [htB.1])
      · exact le_min htA.2 (by linarith [htB.2])
    · intro ht
      change max (-T / 2) (x - T / 2) ≤ t ∧
        t ≤ min (T / 2) (x + T / 2) at ht
      constructor
      · change -T / 2 ≤ t ∧ t ≤ T / 2
        exact ⟨le_trans (le_max_left _ _) ht.1,
          le_trans ht.2 (min_le_left _ _)⟩
      · change -T / 2 ≤ -(x - t) ∧ -(x - t) ≤ T / 2
        have htA1 : -T / 2 ≤ t := le_trans (le_max_left _ _) ht.1
        have htB1 : x - T / 2 ≤ t := le_trans (le_max_right _ _) ht.1
        have htA2 : t ≤ T / 2 := le_trans ht.2 (min_le_left _ _)
        have htB2 : t ≤ x + T / 2 := le_trans ht.2 (min_le_right _ _)
        constructor <;> linarith
  rw [hconv x, hconv 0, hset x, hset 0]
  rw [Real.volume_real_Icc, Real.volume_real_Icc]
  have hlen :
      max (min (T / 2) (x + T / 2) - max (-T / 2) (x - T / 2)) 0 =
        max (T - |x|) 0 := by
    rcases le_total 0 x with hx | hx
    · by_cases hxt : x ≤ T
      · have hleft : -T / 2 ≤ x - T / 2 := by linarith
        have hright : T / 2 ≤ x + T / 2 := by linarith
        rw [max_eq_right hleft, min_eq_left hright]
        rw [abs_of_nonneg hx]
        congr 1
        ring
      · have hleft : -T / 2 ≤ x - T / 2 := by linarith
        have hright : T / 2 ≤ x + T / 2 := by linarith
        rw [max_eq_right hleft, min_eq_left hright]
        rw [abs_of_nonneg hx]
        have hnonpos : T - x ≤ 0 := by linarith
        have hdiff : T / 2 - (x - T / 2) = T - x := by ring
        rw [hdiff, max_eq_right hnonpos]
    · have hx' : x ≤ 0 := hx
      by_cases hxt : -x ≤ T
      · have hleft : x - T / 2 ≤ -T / 2 := by linarith
        have hright : x + T / 2 ≤ T / 2 := by linarith
        rw [max_eq_left hleft, min_eq_right hright]
        rw [abs_of_nonpos hx']
        congr 1
        ring_nf
      · have hleft : x - T / 2 ≤ -T / 2 := by linarith
        have hright : x + T / 2 ≤ T / 2 := by linarith
        rw [max_eq_left hleft, min_eq_right hright]
        rw [abs_of_nonpos hx']
        have hnonpos : T + x ≤ 0 := by linarith
        have hdiff : x + T / 2 - -T / 2 = T + x := by ring
        have hdiff' : T - -x = T + x := by ring
        rw [hdiff, hdiff', max_eq_right hnonpos]
  rw [hlen]
  have hden :
      max (min (T / 2) (0 + T / 2) - max (-T / 2) (0 - T / 2)) 0 = T := by
    have hneg : -(T / 2) = -T / 2 := by ring
    simp only [zero_add, zero_sub, min_self, hneg, max_self]
    have hpos : 0 ≤ T / 2 - -T / 2 := by linarith [hT]
    rw [max_eq_left hpos]
    ring
  rw [hden]
  unfold chapter08TriangularAutocorrelation
  by_cases hnonneg : 0 ≤ T - |x|
  · have hratio : 1 - |x| / T = (T - |x|) / T := by
      field_simp [ne_of_gt hT]
    rw [hratio, max_eq_left hnonneg,
      max_eq_left (div_nonneg hnonneg hT.le)]
  · have hnonpos : T - |x| ≤ 0 := le_of_not_ge hnonneg
    have hleft : 1 - |x| / T ≤ 0 := by
      apply sub_nonpos.mpr
      apply (le_div_iff₀ hT).2
      simpa using hnonpos
    rw [max_eq_right hleft, max_eq_right hnonpos]
    simp

/- The source already specifies the removable value `sinc 0 = 1`; `chapter08Sinc` records that
   convention as a total Lean function. -/
theorem chapter08_triangular_fourier_transform
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    chapter08CosineTransform (chapter08TriangularAutocorrelation T) t =
      T * (chapter08Sinc (T * t / 2)) ^ 2 := by
  let g : ℝ → ℝ := fun x =>
    chapter08TriangularAutocorrelation T x * Real.cos (t * x)
  have hcont : Continuous g := by
    dsimp [g]
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hcompact : HasCompactSupport g := by
    dsimp [g]
    change HasCompactSupport
      (chapter08TriangularAutocorrelation T * fun x : ℝ => Real.cos (t * x))
    have htri : HasCompactSupport (chapter08TriangularAutocorrelation T) := by
      refine (isCompact_Icc : IsCompact (Icc (-T) T)).of_isClosed_subset
        (isClosed_tsupport _) ?_
      apply closure_minimal
      · intro x hx
        change chapter08TriangularAutocorrelation T x ≠ 0 at hx
        constructor
        · by_contra hleft
          have hxlt : x < -T := lt_of_not_ge hleft
          have hxabs : |x| = -x := abs_of_neg (lt_trans hxlt (by linarith))
          have hratio : 1 < |x| / T := by
            rw [hxabs]
            apply (lt_div_iff₀ hT).2
            linarith
          have hzero : chapter08TriangularAutocorrelation T x = 0 := by
            rw [chapter08TriangularAutocorrelation,
              max_eq_right (le_of_lt (sub_neg.mpr hratio))]
          exact (hx hzero).elim
        · by_contra hright
          have hxgt : T < x := lt_of_not_ge hright
          have hxabs : |x| = x := abs_of_pos (lt_trans hT hxgt)
          have hratio : 1 < |x| / T := by
            rw [hxabs]
            apply (lt_div_iff₀ hT).2
            linarith
          have hzero : chapter08TriangularAutocorrelation T x = 0 := by
            rw [chapter08TriangularAutocorrelation,
              max_eq_right (le_of_lt (sub_neg.mpr hratio))]
          exact (hx hzero).elim
      · exact isClosed_Icc
    exact htri.mul_right
  have hint : Integrable g :=
    hcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcompact
  have htail : IntegrableOn g (Ioi T) := hint.integrableOn
  have htail_zero : ∀ x ∈ Ioi T, g x = 0 := by
    intro x hx
    change T < x at hx
    dsimp [g]
    rw [chapter08TriangularAutocorrelation]
    have hratio : 1 < |x| / T := by
      rw [abs_of_pos (lt_trans hT hx)]
      apply (lt_div_iff₀ hT).2
      linarith
    rw [max_eq_right (le_of_lt (sub_neg.mpr hratio)), zero_mul]
  have hIoi : (∫ x : ℝ in Ioi 0, g x) =
      ∫ x : ℝ in (0 : ℝ)..T, g x := by
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (μ := (volume : Measure ℝ)) (f := g) (a := (0 : ℝ)) (b := T)
      hint.integrableOn htail
    rw [intervalIntegral.integral_of_le hT.le] at hadd
    have hzero : (∫ x : ℝ in Ioi T, g x) = 0 :=
      integral_eq_zero_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi htail_zero)
    rw [hzero, add_zero] at hadd
    simpa only [intervalIntegral.integral_of_le hT.le] using hadd.symm
  have hfull : (∫ x : ℝ, g x) = 2 * ∫ x : ℝ in Ioi 0, g x := by
    have habs := integral_comp_abs (f := g)
    have heq : (∫ x : ℝ, g |x|) = ∫ x : ℝ, g x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : 0 ≤ x
      · simp [abs_of_nonneg hx]
      · have hx' : x < 0 := lt_of_not_ge hx
        simp [abs_of_neg hx', g, chapter08TriangularAutocorrelation,
          Real.cos_neg, abs_neg]
    rw [← heq]
    exact habs
  by_cases ht : t = 0
  · subst t
    unfold chapter08CosineTransform
    change (∫ x : ℝ, g x) = T * (chapter08Sinc (T * 0 / 2)) ^ 2
    have hA' : (∫ x : ℝ in Ioi 0,
        chapter08TriangularAutocorrelation T x) = T / 2 := by
      calc
        (∫ x : ℝ in Ioi 0,
            chapter08TriangularAutocorrelation T x) =
            ∫ x : ℝ in Ioi 0, g x := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          simp [g]
        _ = ∫ x : ℝ in (0 : ℝ)..T, g x := hIoi
        _ =
            ∫ x : ℝ in (0 : ℝ)..T, (1 - x / T) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hT.le] at hx
          have hx0 : 0 ≤ x := hx.1
          have hxT : x ≤ T := hx.2
          have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
          simp only [g, zero_mul, Real.cos_zero, mul_one]
          unfold chapter08TriangularAutocorrelation
          rw [hratio]
          have hlin : 0 ≤ 1 - x / T := by
            apply sub_nonneg.mpr
            exact (div_le_iff₀ hT).2 (by simpa using hxT)
          rw [max_eq_left hlin]
        _ = T / 2 := by
          change (∫ x : ℝ in (0 : ℝ)..T, (1 : ℝ) - id x / T) = T / 2
          have hid : (∫ x : ℝ in (0 : ℝ)..T, id x) = T ^ 2 / 2 := by
            have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
                HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
              intro x hx
              convert (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;> try rfl
              · norm_num [id]
            have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (a := (0 : ℝ)) (b := T) hderiv
              ((continuous_id.intervalIntegrable 0 T))
            norm_num at hcalc ⊢
          rw [intervalIntegral.integral_sub
            (intervalIntegrable_const :
              IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T)
            ((continuous_id.div_const T).intervalIntegrable 0 T),
            intervalIntegral.integral_const, intervalIntegral.integral_div, hid]
          field_simp
          ring
    have hG : (∫ x : ℝ in Ioi 0, g x) = T / 2 := by
      calc
        (∫ x : ℝ in Ioi 0, g x) =
            ∫ x : ℝ in Ioi 0, chapter08TriangularAutocorrelation T x := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          simp [g]
        _ = T / 2 := hA'
    rw [hfull, hG]
    simpa [chapter08Sinc] using (show 2 * (T / 2) = T by ring)
  · unfold chapter08CosineTransform
    change (∫ x : ℝ, g x) = T * (chapter08Sinc (T * t / 2)) ^ 2
    have hinterval : (∫ x : ℝ in (0 : ℝ)..T, g x) =
        (1 - Real.cos (T * t)) / (T * t ^ 2) := by
      have hlincont : Continuous
          (fun x : ℝ => (1 - x / T) * Real.cos (t * x)) := by
        fun_prop
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
          HasDerivAt (fun y : ℝ =>
            (1 - y / T) * (Real.sin (t * y) / t) -
              Real.cos (t * y) / (T * t ^ 2))
            ((1 - x / T) * Real.cos (t * x)) x := by
        intro x hx
        have hs : HasDerivAt (fun y : ℝ => Real.sin (t * y))
            (t * Real.cos (t * x)) x := by
          simpa [Function.comp_def, mul_comm] using
            (Real.hasDerivAt_sin (t * x)).comp x
              ((hasDerivAt_id x).const_mul t)
        have hc : HasDerivAt (fun y : ℝ => Real.cos (t * y))
            (-(t * Real.sin (t * x))) x := by
          simpa [Function.comp_def, mul_comm] using
            (Real.hasDerivAt_cos (t * x)).comp x
              ((hasDerivAt_id x).const_mul t)
        have hq : HasDerivAt (fun y : ℝ => 1 - y / T) (-1 / T) x := by
          convert (hasDerivAt_const x (1 : ℝ)).sub
              ((hasDerivAt_id x).div_const T) using 1
          · rfl
          · rfl
          · funext y
            simp [id, div_eq_mul_inv]
          · ring
        let P : ℝ → ℝ := fun y =>
          (1 - y / T) * (Real.sin (t * y) / t) -
            Real.cos (t * y) / (T * t ^ 2)
        change HasDerivAt P ((1 - x / T) * Real.cos (t * x)) x
        dsimp [P]
        convert (hq.mul (hs.div_const t)).sub
            (hc.div_const (T * t ^ 2)) using 1
        · rfl
        · rfl
        · funext y
          rfl
        · field_simp [ne_of_gt hT, ht]
          ring
      have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := T) hderiv (hlincont.intervalIntegrable 0 T)
      have hcalc' :
          (∫ x : ℝ in (0 : ℝ)..T,
              (1 - x / T) * Real.cos (t * x)) =
            (1 - Real.cos (T * t)) / (T * t ^ 2) := by
        convert hcalc using 1
        field_simp [ne_of_gt hT, ht]
        norm_num; ring
      calc
        (∫ x : ℝ in (0 : ℝ)..T, g x) =
            ∫ x : ℝ in (0 : ℝ)..T,
              (1 - x / T) * Real.cos (t * x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hT.le] at hx
          have hx0 : 0 ≤ x := hx.1
          have hxT : x ≤ T := hx.2
          have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
          dsimp [g]
          unfold chapter08TriangularAutocorrelation
          rw [hratio]
          have hlin : 0 ≤ 1 - x / T := by
            apply sub_nonneg.mpr
            exact (div_le_iff₀ hT).2 (by simpa using hxT)
          rw [max_eq_left hlin]
        _ = (1 - Real.cos (T * t)) / (T * t ^ 2) := hcalc'
    rw [hfull, hIoi, hinterval]
    have hu : T * t / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero (ne_of_gt hT) ht) (by norm_num)
    have hcos : Real.cos (T * t) = 1 - 2 * Real.sin (T * t / 2) ^ 2 := by
      convert Real.cos_two_mul_eq_one_sub (T * t / 2) using 1; ring_nf
    rw [hcos]
    simpa [chapter08Sinc, hu] using
      (show 2 * ((1 - (1 - 2 * Real.sin (T * t / 2) ^ 2)) /
          (T * t ^ 2)) = T * (Real.sin (T * t / 2) / (T * t / 2)) ^ 2 by
        field_simp [ne_of_gt hT, ht]
        ring)

theorem chapter08_triangular_angular_fourier_transform
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    chapter08FourierTransform (chapter08TriangularAutocorrelation T) t =
      (T * (chapter08Sinc (T * t / 2)) ^ 2 : ℂ) := by
  have hcont : Continuous (chapter08TriangularAutocorrelation T) := by
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hcompact : HasCompactSupport (chapter08TriangularAutocorrelation T) := by
    refine (isCompact_Icc : IsCompact (Icc (-T) T)).of_isClosed_subset
      (isClosed_tsupport _) ?_
    apply closure_minimal
    · intro x hx
      change chapter08TriangularAutocorrelation T x ≠ 0 at hx
      constructor
      · by_contra hleft
        have hxlt : x < -T := lt_of_not_ge hleft
        have hxabs : |x| = -x := abs_of_neg (lt_trans hxlt (by linarith))
        have hratio : 1 < |x| / T := by
          rw [hxabs]
          apply (lt_div_iff₀ hT).2
          linarith
        have hzero : chapter08TriangularAutocorrelation T x = 0 := by
          rw [chapter08TriangularAutocorrelation,
            max_eq_right (le_of_lt (sub_neg.mpr hratio))]
        exact (hx hzero).elim
      · by_contra hright
        have hxgt : T < x := lt_of_not_ge hright
        have hxabs : |x| = x := abs_of_pos (lt_trans hT hxgt)
        have hratio : 1 < |x| / T := by
          rw [hxabs]
          apply (lt_div_iff₀ hT).2
          linarith
        have hzero : chapter08TriangularAutocorrelation T x = 0 := by
          rw [chapter08TriangularAutocorrelation,
            max_eq_right (le_of_lt (sub_neg.mpr hratio))]
        exact (hx hzero).elim
    · exact isClosed_Icc
  have hint : Integrable (chapter08TriangularAutocorrelation T) :=
    hcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ))
      hcompact
  rw [chapter08_fourier_transform_eq_cosine_of_even hint chapter08_triangular_even t]
  rw [chapter08_triangular_fourier_transform hT t]
  simp

theorem chapter08_triangular_fourier_nonnegative
    {T : ℝ} (hT : 0 < T) (t : ℝ) :
    0 ≤ chapter08CosineTransform (chapter08TriangularAutocorrelation T) t := by
  rw [chapter08_triangular_fourier_transform hT t]
  exact mul_nonneg (le_of_lt hT) (sq_nonneg _)

theorem chapter08_triangular_nonnegative {T x : ℝ} :
    0 ≤ chapter08TriangularAutocorrelation T x := by
  exact le_max_right _ _

theorem chapter08_triangular_has_compact_support {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (chapter08TriangularAutocorrelation T) := by
  refine (isCompact_Icc : IsCompact (Icc (-T) T)).of_isClosed_subset
    (isClosed_tsupport _) ?_
  apply closure_minimal
  · intro x hx
    change chapter08TriangularAutocorrelation T x ≠ 0 at hx
    constructor
    · by_contra hleft
      have hxlt : x < -T := lt_of_not_ge hleft
      have hxabs : |x| = -x := abs_of_neg (lt_trans hxlt (by linarith))
      have hratio : 1 < |x| / T := by
        rw [hxabs]
        apply (lt_div_iff₀ hT).2
        linarith
      have hzero : chapter08TriangularAutocorrelation T x = 0 := by
        rw [chapter08TriangularAutocorrelation, max_eq_right (le_of_lt (sub_neg.mpr hratio))]
      exact (hx hzero).elim
    · by_contra hright
      have hxgt : T < x := lt_of_not_ge hright
      have hxabs : |x| = x := abs_of_pos (lt_trans hT hxgt)
      have hratio : 1 < |x| / T := by
        rw [hxabs]
        apply (lt_div_iff₀ hT).2
        linarith
      have hzero : chapter08TriangularAutocorrelation T x = 0 := by
        rw [chapter08TriangularAutocorrelation, max_eq_right (le_of_lt (sub_neg.mpr hratio))]
      exact (hx hzero).elim
  · exact isClosed_Icc

theorem chapter08_triangular_positive_type {T : ℝ} (hT : 0 < T) :
    Chapter08PositiveType (chapter08TriangularAutocorrelation T) := by
  have hcont : Continuous (chapter08TriangularAutocorrelation T) := by
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hcompact := chapter08_triangular_has_compact_support hT
  have hint : Integrable (chapter08TriangularAutocorrelation T) :=
    hcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcompact
  refine ⟨hcont, hint, ?_⟩
  intro t
  have hfourier := chapter08_fourier_transform_eq_cosine_of_even hint
    chapter08_triangular_even t
  have hre :
      (chapter08FourierTransform (chapter08TriangularAutocorrelation T) t).re =
        chapter08CosineTransform (chapter08TriangularAutocorrelation T) t := by
    rw [hfourier]
    simp
  have hcustom :
      0 ≤ (chapter08FourierTransform (chapter08TriangularAutocorrelation T) t).re ∧
        (chapter08FourierTransform (chapter08TriangularAutocorrelation T) t).im = 0 := by
    refine ⟨?_, ?_⟩
    · rw [hre]
      exact chapter08_triangular_fourier_nonnegative hT t
    · rw [hfourier]
      simp
  rw [← chapter08_fourier_transform_eq_chapter05
    (chapter08TriangularAutocorrelation T) t]
  exact ⟨hcustom.2, hcustom.1⟩

theorem chapter08_boundedVariationOn_sub {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x - g x) s := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((f - g) (u (i + 1))) ((f - g) (u i))) ≤
      ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [Pi.sub_apply, sub_eq_add_neg] using
        (edist_add_add_le (f (u (i + 1))) (-g (u (i + 1)))
          (f (u i)) (-g (u i)))
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s := by
      gcongr
      · exact eVariationOn.sum_le hu hus
      · exact eVariationOn.sum_le hu hus

theorem chapter08_boundedVariationOn_add {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((fun x => f x + g x) (u (i + 1)))
          ((fun x => f x + g x) (u i))) ≤
      ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using
        (edist_add_add_le (f (u (i + 1))) (g (u (i + 1)))
          (f (u i)) (g (u i)))
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s := by
      gcongr
      · exact eVariationOn.sum_le hu hus
      · exact eVariationOn.sum_le hu hus

theorem chapter08_step_boundedVariationOn_le
    {r c a b : ℝ} (hc : 0 ≤ c) :
    BoundedVariationOn (fun x : ℝ => if r ≤ x then c else 0) (Set.uIcc a b) := by
  have hmono : Monotone (fun x : ℝ => if r ≤ x then c else 0) := by
    intro x y hxy
    by_cases hx : r ≤ x
    · simp [hx, le_trans hx hxy]
    · by_cases hy : r ≤ y
      · simp [hx, hy, hc]
      · simp [hx, hy]
  apply (hmono.monotoneOn (Set.uIcc a b)).boundedVariationOn (C := c)
  intro x hx
  by_cases h : r ≤ x
  · simp [h, abs_of_nonneg hc]
  · simpa [h] using hc

theorem chapter08_step_boundedVariationOn_lt
    {r c a b : ℝ} (hc : 0 ≤ c) :
    BoundedVariationOn (fun x : ℝ => if r < x then c else 0) (Set.uIcc a b) := by
  have hmono : Monotone (fun x : ℝ => if r < x then c else 0) := by
    intro x y hxy
    by_cases hx : r < x
    · simp [hx, lt_of_lt_of_le hx hxy]
    · by_cases hy : r < y
      · simp [hx, hy, hc]
      · simp [hx, hy]
  apply (hmono.monotoneOn (Set.uIcc a b)).boundedVariationOn (C := c)
  intro x hx
  by_cases h : r < x
  · simp [h, abs_of_nonneg hc]
  · simpa [h] using hc

theorem chapter08_triangular_piecewiseC2 {T : ℝ} (hT : 0 < T) :
    Chapter08PiecewiseC2 (chapter08TriangularAutocorrelation T) := by
  refine ⟨{-T, 0, T}, ?_⟩
  intro x hx
  have hxneg : x ≠ -T := by
    intro h
    apply hx
    simp [h]
  have hxzero : x ≠ 0 := by
    intro h
    apply hx
    simp [h]
  have hxpos : x ≠ T := by
    intro h
    apply hx
    simp [h]
  rcases lt_or_ge x (-T) with hleft | hnotleft
  · let ε : ℝ := (-T - x) / 2
    refine ⟨ε, by dsimp [ε]; linarith, ?_⟩
    have hsimple : ContDiffOn ℝ 2 (fun _ : ℝ => (0 : ℝ))
        (Set.Ioo (x - ε) (x + ε)) := by fun_prop
    apply hsimple.congr
    intro y hy
    rcases hy with ⟨hy₁, hy₂⟩
    have hyneg : y < -T := by
      dsimp [ε] at hy₁ hy₂
      linarith [hleft, hy₂]
    unfold chapter08TriangularAutocorrelation
    rw [abs_of_neg (lt_trans hyneg (by linarith [hT]))]
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hT).2
    linarith
  · have hgtleft : -T < x := lt_of_le_of_ne hnotleft (Ne.symm hxneg)
    rcases lt_or_ge x 0 with hnegative | hnotnegative
    · let ε : ℝ := min (x + T) (-x) / 2
      refine ⟨ε, by
        dsimp [ε]
        have h₁ : 0 < x + T := by linarith
        have h₂ : 0 < -x := by linarith
        positivity, ?_⟩
      have hsimple : ContDiffOn ℝ 2 (fun y : ℝ => 1 + y / T)
          (Set.Ioo (x - ε) (x + ε)) := by fun_prop
      apply hsimple.congr
      intro y hy
      rcases hy with ⟨hy₁, hy₂⟩
      have hyleft : -T < y := by
        dsimp [ε] at hy₁ hy₂
        have hmin : min (x + T) (-x) ≤ x + T := min_le_left _ _
        linarith [hy₁]
      have hyright : y < 0 := by
        dsimp [ε] at hy₁ hy₂
        have hmin : min (x + T) (-x) ≤ -x := min_le_right _ _
        linarith [hy₂]
      unfold chapter08TriangularAutocorrelation
      rw [abs_of_neg hyright]
      rw [show 1 - -y / T = 1 + y / T by ring]
      apply max_eq_left
      have hratio : -1 < y / T := (lt_div_iff₀ hT).2 (by linarith)
      linarith
    · have hgtzero : 0 < x := lt_of_le_of_ne hnotnegative (Ne.symm hxzero)
      rcases lt_or_ge x T with hinside | houtside
      · let ε : ℝ := min x (T - x) / 2
        refine ⟨ε, by
          dsimp [ε]
          have h₁ : 0 < x := hgtzero
          have h₂ : 0 < T - x := by linarith
          positivity, ?_⟩
        have hsimple : ContDiffOn ℝ 2 (fun y : ℝ => 1 - y / T)
            (Set.Ioo (x - ε) (x + ε)) := by fun_prop
        apply hsimple.congr
        intro y hy
        rcases hy with ⟨hy₁, hy₂⟩
        have hyleft : 0 < y := by
          dsimp [ε] at hy₁ hy₂
          have hmin : min x (T - x) ≤ x := min_le_left _ _
          linarith [hy₁]
        have hyright : y < T := by
          dsimp [ε] at hy₁ hy₂
          have hmin : min x (T - x) ≤ T - x := min_le_right _ _
          linarith [hy₂]
        unfold chapter08TriangularAutocorrelation
        rw [abs_of_pos hyleft]
        apply max_eq_left
        apply sub_nonneg.mpr
        apply (div_le_iff₀ hT).2
        linarith
      · have hgt : T < x := lt_of_le_of_ne houtside (Ne.symm hxpos)
        let ε : ℝ := (x - T) / 2
        refine ⟨ε, by dsimp [ε]; linarith, ?_⟩
        have hsimple : ContDiffOn ℝ 2 (fun _ : ℝ => (0 : ℝ))
            (Set.Ioo (x - ε) (x + ε)) := by fun_prop
        apply hsimple.congr
        intro y hy
        rcases hy with ⟨hy₁, hy₂⟩
        have hygt : T < y := by
          dsimp [ε] at hy₁ hy₂
          linarith [hy₂]
        unfold chapter08TriangularAutocorrelation
        apply max_eq_right
        apply sub_nonpos.mpr
        apply (le_div_iff₀ hT).2
        have : |y| = y := abs_of_pos (lt_trans hT hygt)
        rw [this]
        linarith

theorem chapter08_triangular_right_derivative {T x : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (chapter08TriangularAutocorrelation T)
      ((if -T ≤ x then 1 / T else 0) +
        (if T ≤ x then 1 / T else 0) -
          (if 0 ≤ x then 2 / T else 0)) (Set.Ici x) x := by
  have hzeroL : ∀ y : ℝ, y ≤ -T →
      chapter08TriangularAutocorrelation T y = 0 := by
    intro y hy
    unfold chapter08TriangularAutocorrelation
    have hyneg : y < 0 := by linarith
    rw [abs_of_neg hyneg]
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hT).2
    linarith
  have hneg : ∀ y : ℝ, -T ≤ y → y ≤ 0 →
      chapter08TriangularAutocorrelation T y = 1 + y / T := by
    intro y hyl hyu
    unfold chapter08TriangularAutocorrelation
    rw [abs_of_nonpos hyu]
    rw [show 1 - -y / T = 1 + y / T by ring]
    apply max_eq_left
    have hratio : -1 ≤ y / T := (le_div_iff₀ hT).2 (by linarith)
    linarith
  have hpos : ∀ y : ℝ, 0 ≤ y → y ≤ T →
      chapter08TriangularAutocorrelation T y = 1 - y / T := by
    intro y hyl hyu
    unfold chapter08TriangularAutocorrelation
    rw [abs_of_nonneg hyl]
    apply max_eq_left
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hT).2 (by linarith)
  have hzeroR : ∀ y : ℝ, T ≤ y →
      chapter08TriangularAutocorrelation T y = 0 := by
    intro y hy
    unfold chapter08TriangularAutocorrelation
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hT).2
    have hyabs : |y| = y := abs_of_nonneg (le_trans hT.le hy)
    rw [hyabs]
    linarith
  by_cases hleft : x < -T
  · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Ici x)]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hleft)] with y hy
      exact hzeroL y (le_of_lt hy)
    have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Ici x) x :=
      (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
    have hxEq := hzeroL x (le_of_lt hleft)
    have hTnot : ¬ T ≤ x := by linarith
    have h0not : ¬ 0 ≤ x := by linarith
    simpa [not_le.mpr hleft, hTnot, h0not] using
      hder.congr_of_eventuallyEq hEq hxEq
  · have hleft' : -T ≤ x := le_of_not_gt hleft
    by_cases hnegative : x < 0
    · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Ici x)]
          (fun y : ℝ => 1 + y / T) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hnegative)] with y hy₁ hy₂
        exact hneg y (hleft'.trans hy₁) hy₂.le
      have hder : HasDerivWithinAt (fun y : ℝ => 1 + y / T) (1 / T)
          (Set.Ici x) x := by
        convert ((hasDerivAt_const x (1 : ℝ)).add
          ((hasDerivAt_id x).div_const T)).hasDerivWithinAt using 1
        · rfl
        · rfl
        · funext y
          simp [id, div_eq_mul_inv]
        · ring
      have hxEq := hneg x hleft' (le_of_lt hnegative)
      have hTnot : ¬ T ≤ x := by linarith
      have h0not : ¬ 0 ≤ x := by linarith
      simpa [hleft', hTnot, h0not] using
        hder.congr_of_eventuallyEq hEq hxEq
    · have hxnonnegative : 0 ≤ x := le_of_not_gt hnegative
      by_cases hxzero : x = 0
      · subst x
        have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin 0 (Set.Ici (0 : ℝ))]
            (fun y : ℝ => 1 - y / T) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with y hy₁ hy₂
          exact hpos y hy₁ hy₂.le
        have hder : HasDerivWithinAt (fun y : ℝ => 1 - y / T) (-1 / T)
            (Set.Ici (0 : ℝ)) 0 := by
          convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
            ((hasDerivAt_id (0 : ℝ)).div_const T)).hasDerivWithinAt using 1
          · rfl
          · rfl
          · funext y
            simp [id, div_eq_mul_inv]
          · ring
        have hxEq := hpos 0 (by norm_num) hT.le
        have hminus : -T ≤ (0 : ℝ) := by linarith
        have hTnot : ¬ T ≤ (0 : ℝ) := by linarith
        have hcoef :
            (if -T ≤ (0 : ℝ) then 1 / T else 0) +
                (if T ≤ (0 : ℝ) then 1 / T else 0) -
              (if 0 ≤ (0 : ℝ) then 2 / T else 0) = -1 / T := by
          simp [hminus, hTnot]
          ring
        rw [hcoef]
        exact hder.congr_of_eventuallyEq hEq hxEq
      · have hxpositive : 0 < x := lt_of_le_of_ne hxnonnegative (Ne.symm hxzero)
        by_cases hinside : x < T
        · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Ici x)]
              (fun y : ℝ => 1 - y / T) := by
            filter_upwards [mem_nhdsWithin_of_mem_nhds
              (Ioo_mem_nhds hxpositive hinside)] with y hy
            exact hpos y (le_of_lt hy.1) (le_of_lt hy.2)
          have hder : HasDerivWithinAt (fun y : ℝ => 1 - y / T) (-1 / T)
              (Set.Ici x) x := by
            convert ((hasDerivAt_const x (1 : ℝ)).sub
              ((hasDerivAt_id x).div_const T)).hasDerivWithinAt using 1
            · rfl
            · rfl
            · funext y
              simp [id, div_eq_mul_inv]
            · ring
          have hxEq := hpos x hxnonnegative hinside.le
          have hTnot : ¬ T ≤ x := by linarith
          have hcoef :
              (if -T ≤ x then 1 / T else 0) +
                  (if T ≤ x then 1 / T else 0) -
                (if 0 ≤ x then 2 / T else 0) = -1 / T := by
            simp [hleft', hxnonnegative, hTnot]
            ring
          rw [hcoef]
          exact hder.congr_of_eventuallyEq hEq hxEq
        · have hTle : T ≤ x := le_of_not_gt hinside
          have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Ici x)]
              (fun _ : ℝ => (0 : ℝ)) := by
            have hU : Set.Ioi (-T) ∈ nhds x := Ioi_mem_nhds (by linarith)
            filter_upwards [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds hU] with y hy₁ hy₂
            have hyx : x ≤ y := hy₁
            exact hzeroR y (le_trans hTle hyx)
          have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
              (Set.Ici x) x := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
          have hxEq := hzeroR x hTle
          have hminus : -T ≤ x := by linarith
          have hzero : 0 ≤ x := hxnonnegative
          have hcoef :
              (if -T ≤ x then 1 / T else 0) +
                  (if T ≤ x then 1 / T else 0) -
                (if 0 ≤ x then 2 / T else 0) = 0 := by
            simp [hminus, hTle, hzero]
            ring
          rw [hcoef]
          exact hder.congr_of_eventuallyEq hEq hxEq

theorem chapter08_triangular_left_derivative {T x : ℝ} (hT : 0 < T) :
    HasDerivWithinAt (chapter08TriangularAutocorrelation T)
      ((if -T < x then 1 / T else 0) +
        (if T < x then 1 / T else 0) -
          (if 0 < x then 2 / T else 0)) (Set.Iic x) x := by
  have hzeroL : ∀ y : ℝ, y ≤ -T →
      chapter08TriangularAutocorrelation T y = 0 := by
    intro y hy
    unfold chapter08TriangularAutocorrelation
    have hyneg : y < 0 := by linarith
    rw [abs_of_neg hyneg]
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hT).2
    linarith
  have hneg : ∀ y : ℝ, -T ≤ y → y ≤ 0 →
      chapter08TriangularAutocorrelation T y = 1 + y / T := by
    intro y hyl hyu
    unfold chapter08TriangularAutocorrelation
    rw [abs_of_nonpos hyu]
    rw [show 1 - -y / T = 1 + y / T by ring]
    apply max_eq_left
    have hratio : -1 ≤ y / T := (le_div_iff₀ hT).2 (by linarith)
    linarith
  have hpos : ∀ y : ℝ, 0 ≤ y → y ≤ T →
      chapter08TriangularAutocorrelation T y = 1 - y / T := by
    intro y hyl hyu
    unfold chapter08TriangularAutocorrelation
    rw [abs_of_nonneg hyl]
    apply max_eq_left
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hT).2 (by linarith)
  have hzeroR : ∀ y : ℝ, T ≤ y →
      chapter08TriangularAutocorrelation T y = 0 := by
    intro y hy
    unfold chapter08TriangularAutocorrelation
    apply max_eq_right
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hT).2
    have hyabs : |y| = y := abs_of_nonneg (le_trans hT.le hy)
    rw [hyabs]
    linarith
  by_cases hleft : x ≤ -T
  · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Iic x)]
        (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : x < 0))] with y hy₁ hy₂
      exact hzeroL y (hy₁.trans hleft)
    have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic x) x :=
      (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
    have hxEq := hzeroL x hleft
    have hleftnot : ¬ -T < x := by linarith
    have h0not : ¬ 0 < x := by linarith
    have hTnot : ¬ T < x := by linarith
    simpa [hleftnot, hTnot, h0not] using
      hder.congr_of_eventuallyEq hEq hxEq
  · have hleft' : -T < x := lt_of_not_ge hleft
    by_cases hnonpos : x ≤ 0
    · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Iic x)]
          (fun y : ℝ => 1 + y / T) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hleft')] with y hy₁ hy₂
        exact hneg y hy₂.le (hy₁.trans hnonpos)
      have hder : HasDerivWithinAt (fun y : ℝ => 1 + y / T) (1 / T)
          (Set.Iic x) x := by
        convert ((hasDerivAt_const x (1 : ℝ)).add
          ((hasDerivAt_id x).div_const T)).hasDerivWithinAt using 1
        · rfl
        · rfl
        · funext y
          simp [id, div_eq_mul_inv]
        · ring
      have hxEq := hneg x hleft'.le hnonpos
      have hTnot : ¬ T < x := by linarith
      have h0not : ¬ 0 < x := by linarith
      simpa [hleft', hTnot, h0not] using
        hder.congr_of_eventuallyEq hEq hxEq
    · have hxpositive : 0 < x := lt_of_not_ge hnonpos
      by_cases hinside : x ≤ T
      · have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Iic x)]
            (fun y : ℝ => 1 - y / T) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hxpositive)] with y hy₁ hy₂
          exact hpos y hy₂.le (hy₁.trans hinside)
        have hder : HasDerivWithinAt (fun y : ℝ => 1 - y / T) (-1 / T)
            (Set.Iic x) x := by
          convert ((hasDerivAt_const x (1 : ℝ)).sub
            ((hasDerivAt_id x).div_const T)).hasDerivWithinAt using 1
          · rfl
          · rfl
          · funext y
            simp [id, div_eq_mul_inv]
          · ring
        have hxEq := hpos x hxpositive.le hinside
        have hTnot : ¬ T < x := by linarith
        have hcoef :
            (if -T < x then 1 / T else 0) +
                (if T < x then 1 / T else 0) -
              (if 0 < x then 2 / T else 0) = -1 / T := by
          simp [hleft', hxpositive, hTnot]
          ring
        rw [hcoef]
        exact hder.congr_of_eventuallyEq hEq hxEq
      · have hTlt : T < x := lt_of_not_ge hinside
        have hEq : chapter08TriangularAutocorrelation T =ᶠ[nhdsWithin x (Set.Iic x)]
            (fun _ : ℝ => (0 : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hTlt)] with y hy₁ hy₂
          exact hzeroR y hy₂.le
        have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
            (Set.Iic x) x := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
        have hxEq := hzeroR x hTlt.le
        have hcoef :
            (if -T < x then 1 / T else 0) +
                (if T < x then 1 / T else 0) -
              (if 0 < x then 2 / T else 0) = 0 := by
          simp [hleft', hTlt, hxpositive]
          ring
        rw [hcoef]
        exact hder.congr_of_eventuallyEq hEq hxEq

theorem chapter08_triangular_first_derivative_bounded_variation {T : ℝ} (hT : 0 < T) :
    Chapter08FirstDerivativeBoundedVariation
      (chapter08TriangularAutocorrelation T) := by
  let Dleft : ℝ → ℝ := fun x =>
    (if -T < x then 1 / T else 0) +
      (if T < x then 1 / T else 0) -
        (if 0 < x then 2 / T else 0)
  let Dright : ℝ → ℝ := fun x =>
    (if -T ≤ x then 1 / T else 0) +
      (if T ≤ x then 1 / T else 0) -
        (if 0 ≤ x then 2 / T else 0)
  have h1 : 0 ≤ 1 / T := le_of_lt (one_div_pos.mpr hT)
  have h2 : 0 ≤ 2 / T := by positivity
  refine ⟨Dleft, Dright, ?_, ?_, ?_⟩
  · intro a b
    dsimp [Dleft]
    apply chapter08_boundedVariationOn_sub
    · apply chapter08_boundedVariationOn_add
      · exact chapter08_step_boundedVariationOn_lt h1
      · exact chapter08_step_boundedVariationOn_lt h1
    · exact chapter08_step_boundedVariationOn_lt h2
  · intro a b
    dsimp [Dright]
    apply chapter08_boundedVariationOn_sub
    · apply chapter08_boundedVariationOn_add
      · exact chapter08_step_boundedVariationOn_le h1
      · exact chapter08_step_boundedVariationOn_le h1
    · exact chapter08_step_boundedVariationOn_le h2
  · intro x
    exact ⟨by simpa [Dright] using chapter08_triangular_right_derivative hT,
      by simpa [Dleft] using chapter08_triangular_left_derivative hT⟩

theorem chapter08_triangular_origin_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x : ℝ =>
      |1 - chapter08TriangularAutocorrelation T x| / x) (Set.Ioc 0 1) := by
  apply Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ))
    (s := Set.Ioc (0 : ℝ) 1) (M := 1 / T) (ne_of_lt measure_Ioc_lt_top)
  · have hcont : Continuous (chapter08TriangularAutocorrelation T) := by
      unfold chapter08TriangularAutocorrelation
      fun_prop
    have hmeas : Measurable (fun x : ℝ =>
        |1 - chapter08TriangularAutocorrelation T x| / x) := by
      exact (measurable_const.sub hcont.measurable).norm.div measurable_id
    exact hmeas.aemeasurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxpos : 0 < x := hx.1
    have hxone : x ≤ 1 := hx.2
    by_cases hsmall : x ≤ T
    · have hratio : |x| / T = x / T := by rw [abs_of_pos hxpos]
      have hnonneg : 0 ≤ 1 - x / T := by
        exact sub_nonneg.mpr ((div_le_iff₀ hT).2 (by simpa using hsmall))
      rw [chapter08TriangularAutocorrelation, hratio, max_eq_left hnonneg]
      have hdiff : 1 - (1 - x / T) = x / T := by ring
      rw [hdiff, abs_of_pos (div_pos hxpos hT)]
      have hqpos : 0 < x / T / x := by positivity
      rw [Real.norm_eq_abs, abs_of_pos hqpos]
      field_simp [ne_of_gt hxpos, ne_of_gt hT]
      norm_num
    · have hlarge : T ≤ x := le_of_not_ge hsmall
      have hratio : 1 < |x| / T := by
        rw [abs_of_pos hxpos]
        apply (lt_div_iff₀ hT).2
        linarith
      rw [chapter08TriangularAutocorrelation,
        max_eq_right (le_of_lt (sub_neg.mpr hratio))]
      simp only [sub_zero, abs_one, one_div]
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
      simpa [one_div] using one_div_le_one_div_of_le hT hlarge

theorem chapter08_triangular_bounded_variation {T : ℝ} (hT : 0 < T) :
    ∀ a b : ℝ,
      BoundedVariationOn (chapter08TriangularAutocorrelation T) (Set.uIcc a b) := by
  have hlin : LipschitzWith (Real.toNNReal (1 / T))
      (fun x : ℝ => 1 - |x| / T) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have habs : |(|x| - |y|)| ≤ |x - y| := by
      simpa [Real.norm_eq_abs] using (norm_abs_sub_abs x y)
    rw [Real.dist_eq, Real.dist_eq]
    rw [show (1 - |x| / T) - (1 - |y| / T) = (|y| - |x|) / T by ring]
    rw [abs_div, abs_of_pos hT]
    apply (div_le_iff₀ hT).2
    calc
      |(|y| - |x|)| ≤ |x - y| := by simpa [abs_sub_comm] using habs
      _ = (1 / T) * |x - y| * T := by field_simp
  have hG : LipschitzWith (Real.toNNReal (1 / T))
      (chapter08TriangularAutocorrelation T) := by
    change LipschitzWith (Real.toNNReal (1 / T))
      (fun x : ℝ => max (1 - |x| / T) 0)
    exact hlin.max_const 0
  intro a b
  have hid : BoundedVariationOn id (Set.uIcc a b) := by
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab]
      exact BoundedVariationOn.id_Icc a b
    · rw [uIcc_comm, uIcc_of_le hba]
      exact BoundedVariationOn.id_Icc b a
  simpa [Function.comp_def] using hG.comp_boundedVariationOn hid

theorem chapter08_cosh_inv_bounded_variation {a b : ℝ} :
    BoundedVariationOn (fun x : ℝ => (Real.cosh (x / 2))⁻¹) (Set.uIcc a b) := by
  have hc : ContDiffOn ℝ 1 (fun x : ℝ => Real.cosh (x / 2)) (Set.uIcc a b) := by
    fun_prop
  have hc_inv : ContDiffOn ℝ 1 (fun x : ℝ => (Real.cosh (x / 2))⁻¹)
      (Set.uIcc a b) := by
    apply hc.inv
    intro x hx
    exact ne_of_gt (Real.cosh_pos _)
  exact hc_inv.absolutelyContinuousOnInterval.boundedVariationOn

theorem chapter08_cosh_inv_derivative_bounded_variation {a b : ℝ} :
    BoundedVariationOn
      (fun x : ℝ => -(Real.sinh (x / 2) /
        (2 * Real.cosh (x / 2) ^ 2))) (Set.uIcc a b) := by
  have hs : ContDiffOn ℝ 1 (fun x : ℝ => Real.sinh (x / 2)) (Set.uIcc a b) := by
    fun_prop
  have hc : ContDiffOn ℝ 1 (fun x : ℝ => Real.cosh (x / 2)) (Set.uIcc a b) := by
    fun_prop
  have hden : ContDiffOn ℝ 1
      (fun x : ℝ => 2 * Real.cosh (x / 2) ^ 2) (Set.uIcc a b) := by
    fun_prop
  have hquot : ContDiffOn ℝ 1
      (fun x : ℝ => Real.sinh (x / 2) /
        (2 * Real.cosh (x / 2) ^ 2)) (Set.uIcc a b) := by
    apply hs.div hden
    intro x hx
    positivity
  exact hquot.neg.absolutelyContinuousOnInterval.boundedVariationOn

theorem chapter08_unconditional_triangle_piecewiseC2 {T : ℝ} (hT : 0 < T) :
    Chapter08PiecewiseC2 (chapter08FUnconditionalTriangle T) := by
  rcases chapter08_triangular_piecewiseC2 hT with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro x hx
  rcases hs x hx with ⟨ε, hε, hG⟩
  refine ⟨ε, hε, ?_⟩
  have hC : ContDiffOn ℝ 2 (fun y : ℝ => Real.cosh (y / 2))
      (Set.Ioo (x - ε) (x + ε)) := by
    fun_prop
  exact hG.div hC (fun y hy => ne_of_gt (Real.cosh_pos _))

theorem chapter08_cosh_inv_has_deriv :
    ∀ x : ℝ, HasDerivAt (fun y : ℝ => (Real.cosh (y / 2))⁻¹)
      (-(Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2))) x := by
  intro x
  have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
      (Real.sinh (x / 2) / 2) x := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      (Real.hasDerivAt_cosh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)
  have hi := hc.inv (ne_of_gt (Real.cosh_pos (x / 2)))
  apply hi.congr_deriv
  field_simp [ne_of_gt (Real.cosh_pos (x / 2))]

theorem chapter08_unconditional_triangle_first_derivative_bounded_variation
    {T : ℝ} (hT : 0 < T) :
    Chapter08FirstDerivativeBoundedVariation
      (chapter08FUnconditionalTriangle T) := by
  let Gleft : ℝ → ℝ := fun x =>
    (if -T < x then 1 / T else 0) +
      (if T < x then 1 / T else 0) -
        (if 0 < x then 2 / T else 0)
  let Gright : ℝ → ℝ := fun x =>
    (if -T ≤ x then 1 / T else 0) +
      (if T ≤ x then 1 / T else 0) -
        (if 0 ≤ x then 2 / T else 0)
  let G : ℝ → ℝ := chapter08TriangularAutocorrelation T
  let H : ℝ → ℝ := fun x => (Real.cosh (x / 2))⁻¹
  let H' : ℝ → ℝ := fun x =>
    -(Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2))
  let Dleft : ℝ → ℝ := fun x => Gleft x * H x + G x * H' x
  let Dright : ℝ → ℝ := fun x => Gright x * H x + G x * H' x
  have h1 : 0 ≤ 1 / T := le_of_lt (one_div_pos.mpr hT)
  have h2 : 0 ≤ 2 / T := by positivity
  have hGleft : ∀ a b : ℝ, BoundedVariationOn Gleft (Set.uIcc a b) := by
    intro a b
    dsimp [Gleft]
    apply chapter08_boundedVariationOn_sub
    · apply chapter08_boundedVariationOn_add
      · exact chapter08_step_boundedVariationOn_lt h1
      · exact chapter08_step_boundedVariationOn_lt h1
    · exact chapter08_step_boundedVariationOn_lt h2
  have hGright : ∀ a b : ℝ, BoundedVariationOn Gright (Set.uIcc a b) := by
    intro a b
    dsimp [Gright]
    apply chapter08_boundedVariationOn_sub
    · apply chapter08_boundedVariationOn_add
      · exact chapter08_step_boundedVariationOn_le h1
      · exact chapter08_step_boundedVariationOn_le h1
    · exact chapter08_step_boundedVariationOn_le h2
  have hG : ∀ a b : ℝ, BoundedVariationOn G (Set.uIcc a b) := by
    intro a b
    exact chapter08_triangular_bounded_variation hT a b
  have hDleft : ∀ a b : ℝ, BoundedVariationOn Dleft (Set.uIcc a b) := by
    intro a b
    dsimp [Dleft]
    apply chapter08_boundedVariationOn_add
    · exact (hGleft a b).mul (chapter08_cosh_inv_bounded_variation)
    · exact (hG a b).mul (chapter08_cosh_inv_derivative_bounded_variation)
  have hDright : ∀ a b : ℝ, BoundedVariationOn Dright (Set.uIcc a b) := by
    intro a b
    dsimp [Dright]
    apply chapter08_boundedVariationOn_add
    · exact (hGright a b).mul (chapter08_cosh_inv_bounded_variation)
    · exact (hG a b).mul (chapter08_cosh_inv_derivative_bounded_variation)
  refine ⟨Dleft, Dright, hDleft, hDright, ?_⟩
  intro x
  have hHright : HasDerivWithinAt H (H' x) (Set.Ici x) x := by
    dsimp [H, H']
    exact (chapter08_cosh_inv_has_deriv x).hasDerivWithinAt
  have hHleft : HasDerivWithinAt H (H' x) (Set.Iic x) x := by
    dsimp [H, H']
    exact (chapter08_cosh_inv_has_deriv x).hasDerivWithinAt
  have hright := (chapter08_triangular_right_derivative hT).mul hHright
  have hleft := (chapter08_triangular_left_derivative hT).mul hHleft
  have hEq : ∀ y : ℝ,
      chapter08FUnconditionalTriangle T y = G y * H y := by
    intro y
    dsimp [G, H, chapter08FUnconditionalTriangle]
    field_simp [ne_of_gt (Real.cosh_pos (y / 2))]
  constructor
  · have hright' := hright.congr (fun y hy => hEq y) (hEq x)
    simpa [Dright, Gright, G] using hright'
  · have hleft' := hleft.congr (fun y hy => hEq y) (hEq x)
    simpa [Dleft, Gleft, G] using hleft'

theorem chapter08_unconditional_triangle_origin_integrable {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x : ℝ =>
      |1 - chapter08FUnconditionalTriangle T x| / x) (Set.Ioc 0 1) := by
  have hcont : Continuous (chapter08FUnconditionalTriangle T) := by
    unfold chapter08FUnconditionalTriangle
    have hG : Continuous (chapter08TriangularAutocorrelation T) := by
      unfold chapter08TriangularAutocorrelation
      fun_prop
    exact hG.div (by fun_prop) (fun x => ne_of_gt (Real.cosh_pos _))
  have hcoshC : ContDiffOn ℝ 1 (fun x : ℝ => Real.cosh (x / 2))
      (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  obtain ⟨K, hK⟩ := hcoshC.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (0 : ℝ) 1) isCompact_Icc
  apply Measure.integrableOn_of_bounded (μ := (volume : Measure ℝ))
    (s := Set.Ioc (0 : ℝ) 1) (M := 1 + (K : ℝ) + 1 / T)
    (ne_of_lt measure_Ioc_lt_top)
  · exact (measurable_const.sub hcont.measurable).norm.div measurable_id |>.aemeasurable
      |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxpos : 0 < x := hx.1
    have hxone : x ≤ 1 := hx.2
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxpos.le, hxone⟩
    have hcosh_one : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
    have hcosh_diff :
        |Real.cosh (x / 2) - Real.cosh (0 / 2)| ≤ (K : ℝ) * |x - 0| := by
      have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hdist := hK.dist_le_mul x hxIcc 0 hzero_mem
      simpa only [Real.dist_eq] using hdist
    have hcosh_diff' :
        Real.cosh (x / 2) - 1 ≤ (K : ℝ) * x := by
      have hnonneg : 0 ≤ Real.cosh (x / 2) - 1 := sub_nonneg.mpr hcosh_one
      have hzero : Real.cosh (0 / 2) = 1 := by norm_num
      rw [hzero, abs_of_nonneg hnonneg] at hcosh_diff
      simpa [abs_of_pos hxpos] using hcosh_diff
    by_cases hsmall : x ≤ T
    · have hratio : |x| / T = x / T := by rw [abs_of_pos hxpos]
      have hnonneg : 0 ≤ 1 - x / T := by
        exact sub_nonneg.mpr ((div_le_iff₀ hT).2 (by simpa using hsmall))
      have hFform : chapter08FUnconditionalTriangle T x =
          (1 - x / T) / Real.cosh (x / 2) := by
        unfold chapter08FUnconditionalTriangle chapter08TriangularAutocorrelation
        rw [hratio, max_eq_left hnonneg]
      rw [hFform]
      have hCpos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
      have hnum : 0 ≤ Real.cosh (x / 2) - (1 - x / T) := by
        have hxTnonneg : 0 ≤ x / T := by positivity
        linarith
      have hidentity :
          1 - (1 - x / T) / Real.cosh (x / 2) =
            (Real.cosh (x / 2) - (1 - x / T)) / Real.cosh (x / 2) := by
        field_simp
      rw [hidentity, abs_of_nonneg (div_nonneg hnum hCpos.le),
        Real.norm_eq_abs, abs_of_nonneg
          (div_nonneg (div_nonneg hnum hCpos.le) hxpos.le)]
      apply (div_le_iff₀ hxpos).2
      apply (div_le_iff₀ hCpos).2
      calc
        Real.cosh (x / 2) - (1 - x / T) =
            (Real.cosh (x / 2) - 1) + x / T := by ring
        _ ≤ (K : ℝ) * x + x / T := by linarith
        _ ≤ (1 + (K : ℝ) + 1 / T) * x * Real.cosh (x / 2) := by
          have hKnonneg : 0 ≤ (K : ℝ) := K.coe_nonneg
          have hMnonneg : 0 ≤ 1 + (K : ℝ) + 1 / T := by positivity
          calc
            (K : ℝ) * x + x / T ≤
                (1 + (K : ℝ) + 1 / T) * x := by
              calc
                (K : ℝ) * x + x / T ≤
                    (K : ℝ) * x + x / T + x := by linarith
                _ = (1 + (K : ℝ) + 1 / T) * x := by ring
            _ ≤ (1 + (K : ℝ) + 1 / T) * x * Real.cosh (x / 2) := by
              calc
                (1 + (K : ℝ) + 1 / T) * x =
                    ((1 + (K : ℝ) + 1 / T) * x) * 1 := by ring
                _ ≤ ((1 + (K : ℝ) + 1 / T) * x) * Real.cosh (x / 2) :=
                  mul_le_mul_of_nonneg_left hcosh_one
                    (mul_nonneg hMnonneg hxpos.le)
                _ = (1 + (K : ℝ) + 1 / T) * x * Real.cosh (x / 2) := by ring
    · have hlarge : T ≤ x := le_of_not_ge hsmall
      have hFzero : chapter08FUnconditionalTriangle T x = 0 := by
        unfold chapter08FUnconditionalTriangle chapter08TriangularAutocorrelation
        have hratio : 1 < |x| / T := by
          rw [abs_of_pos hxpos]
          apply (lt_div_iff₀ hT).2
          linarith
        rw [max_eq_right (le_of_lt (sub_neg.mpr hratio)), zero_div]
      rw [hFzero, sub_zero, abs_one, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hxpos)]
      have hinv : 1 / x ≤ 1 / T := one_div_le_one_div_of_le hT hlarge
      have hbound : 1 / T ≤ 1 + (K : ℝ) + 1 / T := by
        linarith [K.coe_nonneg]
      exact hinv.trans hbound

theorem chapter08_unconditional_triangle_admissible {T : ℝ} (hT : 0 < T) :
    Chapter08UnconditionallyAdmissible (chapter08FUnconditionalTriangle T) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      unfold chapter08FUnconditionalTriangle
      rw [chapter08_triangular_even, show -x / 2 = -(x / 2) by ring,
        Real.cosh_neg]
    · unfold chapter08FUnconditionalTriangle
      have hG : Continuous (chapter08TriangularAutocorrelation T) := by
        unfold chapter08TriangularAutocorrelation
        fun_prop
      exact hG.div (by fun_prop) (fun x => ne_of_gt (Real.cosh_pos _))
    · refine (isCompact_Icc : IsCompact (Icc (-T) T)).of_isClosed_subset
        (isClosed_tsupport _) ?_
      apply closure_minimal
      · intro x hx
        change chapter08FUnconditionalTriangle T x ≠ 0 at hx
        constructor
        · by_contra hleft
          have hxlt : x < -T := lt_of_not_ge hleft
          have hxabs : |x| = -x := abs_of_neg (lt_trans hxlt (by linarith))
          have hratio : 1 < |x| / T := by
            rw [hxabs]
            apply (lt_div_iff₀ hT).2
            linarith
          have hzero : chapter08TriangularAutocorrelation T x = 0 := by
            rw [chapter08TriangularAutocorrelation,
              max_eq_right (le_of_lt (sub_neg.mpr hratio))]
          exact (hx (by simp [chapter08FUnconditionalTriangle, hzero])).elim
        · by_contra hright
          have hxgt : T < x := lt_of_not_ge hright
          have hxabs : |x| = x := abs_of_pos (lt_trans hT hxgt)
          have hratio : 1 < |x| / T := by
            rw [hxabs]
            apply (lt_div_iff₀ hT).2
            linarith
          have hzero : chapter08TriangularAutocorrelation T x = 0 := by
            rw [chapter08TriangularAutocorrelation,
              max_eq_right (le_of_lt (sub_neg.mpr hratio))]
          exact (hx (by simp [chapter08FUnconditionalTriangle, hzero])).elim
      · exact isClosed_Icc
    · exact chapter08_unconditional_triangle_piecewiseC2 hT
    · exact chapter08_unconditional_triangle_first_derivative_bounded_variation hT
    · simp [chapter08FUnconditionalTriangle, chapter08_triangular_zero hT]
    · exact chapter08_unconditional_triangle_origin_integrable hT
  · refine ⟨chapter08TriangularAutocorrelation T, chapter08_triangular_even, ?_,
      chapter08_triangular_positive_type hT, ?_⟩
    · intro x
      exact chapter08_triangular_nonnegative
    intro x
    rfl

theorem chapter08_grh_triangle_admissible {T : ℝ} (hT : 0 < T) :
    Chapter08GRHAdmissible (chapter08FGRHTriangle T) := by
  change Chapter08GRHAdmissible (chapter08TriangularAutocorrelation T)
  refine ⟨?_, ?_, chapter08_triangular_positive_type hT⟩
  · refine ⟨chapter08_triangular_even, ?_, ?_, ?_,
        chapter08_triangular_first_derivative_bounded_variation hT, ?_,
        chapter08_triangular_origin_integrable hT⟩
    · unfold chapter08TriangularAutocorrelation
      fun_prop
    · exact chapter08_triangular_has_compact_support hT
    · exact chapter08_triangular_piecewiseC2 hT
    · exact chapter08_triangular_zero hT
  · intro x
    exact chapter08_triangular_nonnegative

theorem chapter08_unconditional_triangle_A {T : ℝ} (hT : 0 < T) :
    chapter08A (chapter08FUnconditionalTriangle T) = T / 2 := by
  have hpoint : ∀ x : ℝ,
      chapter08FUnconditionalTriangle T x * Real.cosh (x / 2) =
        chapter08TriangularAutocorrelation T x := by
    intro x
    dsimp [chapter08FUnconditionalTriangle]
    field_simp [ne_of_gt (Real.cosh_pos _)]
  have hcont : Continuous (chapter08TriangularAutocorrelation T) := by
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hcompact : HasCompactSupport (chapter08TriangularAutocorrelation T) :=
    chapter08_triangular_has_compact_support hT
  have hint : Integrable (chapter08TriangularAutocorrelation T) :=
    hcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcompact
  have htail : IntegrableOn (chapter08TriangularAutocorrelation T) (Ioi T) := by
    exact hint.integrableOn
  have htail_zero : ∀ x ∈ Ioi T,
      chapter08TriangularAutocorrelation T x = 0 := by
    intro x hx
    change T < x at hx
    rw [chapter08TriangularAutocorrelation]
    have hratio : 1 < |x| / T := by
      rw [abs_of_pos (lt_trans hT hx)]
      apply (lt_div_iff₀ hT).2
      linarith
    rw [max_eq_right (le_of_lt (sub_neg.mpr hratio))]
  have hIoi : ∫ x : ℝ in Ioi 0,
      chapter08TriangularAutocorrelation T x =
      ∫ x : ℝ in (0 : ℝ)..T, chapter08TriangularAutocorrelation T x := by
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (μ := (volume : Measure ℝ)) (f := chapter08TriangularAutocorrelation T)
      (a := (0 : ℝ)) (b := T) (hint.integrableOn) htail
    rw [intervalIntegral.integral_of_le hT.le] at hadd
    have hzero : (∫ x : ℝ in Ioi T,
        chapter08TriangularAutocorrelation T x) = 0 :=
      integral_eq_zero_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi htail_zero)
    rw [hzero, add_zero] at hadd
    simpa only [intervalIntegral.integral_of_le hT.le] using hadd.symm
  unfold chapter08A
  have hset : (∫ x : ℝ in Ioi 0,
      chapter08FUnconditionalTriangle T x * Real.cosh (x / 2)) =
      ∫ x : ℝ in Ioi 0, chapter08TriangularAutocorrelation T x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x
  rw [hset, hIoi]
  calc
    (∫ x : ℝ in (0 : ℝ)..T, chapter08TriangularAutocorrelation T x) =
        ∫ x : ℝ in (0 : ℝ)..T, (1 - x / T) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hT.le] at hx
      have hx0 : 0 ≤ x := hx.1
      have hxT : x ≤ T := hx.2
      have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
      unfold chapter08TriangularAutocorrelation
      rw [hratio]
      have hlin : 0 ≤ 1 - x / T := by
        apply sub_nonneg.mpr
        exact (div_le_iff₀ hT).2 (by simpa using hxT)
      rw [max_eq_left hlin]
    _ = T / 2 := by
      change (∫ x : ℝ in (0 : ℝ)..T, (1 : ℝ) - id x / T) = T / 2
      have hid : (∫ x : ℝ in (0 : ℝ)..T, id x) = T ^ 2 / 2 := by
        have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
            HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          intro x hx
          convert (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;> try rfl
          · norm_num [id]
        have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := T) hderiv
          ((continuous_id.intervalIntegrable 0 T))
        norm_num at hcalc ⊢
      rw [intervalIntegral.integral_sub
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T)
        ((continuous_id.div_const T).intervalIntegrable 0 T),
        intervalIntegral.integral_const, intervalIntegral.integral_div, hid]
      field_simp
      ring

theorem chapter08_grh_triangle_A {T : ℝ} (hT : 0 < T) :
    chapter08A (chapter08FGRHTriangle T) =
      4 / T * (Real.cosh (T / 2) - 1) := by
  have hfun : ∀ x : ℝ,
      chapter08FGRHTriangle T x * Real.cosh (x / 2) =
        chapter08TriangularAutocorrelation T x * Real.cosh (x / 2) := by
    intro x
    rfl
  have hcont : Continuous
      (fun x : ℝ => chapter08TriangularAutocorrelation T x * Real.cosh (x / 2)) := by
    unfold chapter08TriangularAutocorrelation
    fun_prop
  have hcompact : HasCompactSupport
      (fun x : ℝ => chapter08TriangularAutocorrelation T x * Real.cosh (x / 2)) := by
    change HasCompactSupport
      (chapter08TriangularAutocorrelation T * fun x : ℝ => Real.cosh (x / 2))
    exact (chapter08_triangular_has_compact_support hT).mul_right
  have hint : Integrable
      (fun x : ℝ => chapter08TriangularAutocorrelation T x * Real.cosh (x / 2)) :=
    hcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcompact
  have htail : IntegrableOn
      (fun x : ℝ => chapter08TriangularAutocorrelation T x * Real.cosh (x / 2))
      (Ioi T) := hint.integrableOn
  have htail_zero : ∀ x ∈ Ioi T,
      chapter08TriangularAutocorrelation T x * Real.cosh (x / 2) = 0 := by
    intro x hx
    change T < x at hx
    rw [chapter08TriangularAutocorrelation]
    have hratio : 1 < |x| / T := by
      rw [abs_of_pos (lt_trans hT hx)]
      apply (lt_div_iff₀ hT).2
      linarith
    rw [max_eq_right (le_of_lt (sub_neg.mpr hratio)), zero_mul]
  have hIoi : ∫ x : ℝ in Ioi 0,
      chapter08TriangularAutocorrelation T x * Real.cosh (x / 2) =
      ∫ x : ℝ in (0 : ℝ)..T,
        chapter08TriangularAutocorrelation T x * Real.cosh (x / 2) := by
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => chapter08TriangularAutocorrelation T x * Real.cosh (x / 2))
      (a := (0 : ℝ)) (b := T) (hint.integrableOn) htail
    rw [intervalIntegral.integral_of_le hT.le] at hadd
    have hzero : (∫ x : ℝ in Ioi T,
        chapter08TriangularAutocorrelation T x * Real.cosh (x / 2)) = 0 :=
      integral_eq_zero_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi htail_zero)
    rw [hzero, add_zero] at hadd
    simpa only [intervalIntegral.integral_of_le hT.le] using hadd.symm
  unfold chapter08A chapter08FGRHTriangle
  rw [hIoi]
  calc
    (∫ x : ℝ in (0 : ℝ)..T,
        chapter08TriangularAutocorrelation T x * Real.cosh (x / 2)) =
        ∫ x : ℝ in (0 : ℝ)..T,
          (1 - x / T) * Real.cosh (x / 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hT.le] at hx
      have hx0 : 0 ≤ x := hx.1
      have hxT : x ≤ T := hx.2
      have hratio : |x| / T = x / T := by rw [abs_of_nonneg hx0]
      change max (1 - |x| / T) 0 * Real.cosh (x / 2) =
        (1 - x / T) * Real.cosh (x / 2)
      rw [hratio]
      have hlin : 0 ≤ 1 - x / T := by
        apply sub_nonneg.mpr
        exact (div_le_iff₀ hT).2 (by simpa using hxT)
      rw [max_eq_left hlin]
    _ = 4 / T * (Real.cosh (T / 2) - 1) := by
      let P : ℝ → ℝ := fun x =>
        2 * Real.sinh (x / 2) - (2 * x / T) * Real.sinh (x / 2) +
          (4 / T) * Real.cosh (x / 2)
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
          HasDerivAt P ((1 - x / T) * Real.cosh (x / 2)) x := by
        intro x hx
        have hs : HasDerivAt (fun y : ℝ => Real.sinh (y / 2))
            (Real.cosh (x / 2) / 2) x :=
          by
            simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
              (Real.hasDerivAt_sinh (x / 2)).comp x
                ((hasDerivAt_id x).div_const 2)
        have hc : HasDerivAt (fun y : ℝ => Real.cosh (y / 2))
            (Real.sinh (x / 2) / 2) x :=
          by
            simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
              (Real.hasDerivAt_cosh (x / 2)).comp x
                ((hasDerivAt_id x).div_const 2)
        dsimp [P]
        convert ((hs.const_mul 2).sub
            ((((hasDerivAt_id x).div_const T).mul hs).const_mul 2)).add
            (hc.const_mul (4 / T)) using 1 <;> try rfl
        · funext y
          dsimp
          ring
        · simp [id]
          ring
      have hlincont : Continuous
          (fun x : ℝ => (1 - x / T) * Real.cosh (x / 2)) :=
        (continuous_const.sub (continuous_id.div_const T)).mul
          (Real.continuous_cosh.comp (continuous_id.div_const 2))
      have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := T) hderiv
        (hlincont.intervalIntegrable 0 T)
      dsimp [P] at hcalc
      norm_num at hcalc ⊢
      convert hcalc using 1; field_simp [ne_of_gt hT]; ring

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter08
