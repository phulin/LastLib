import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory
open scoped Convolution FourierTransform ComplexConjugate RealInnerProductSpace

/-! ## 5.3. Positive type and autocorrelation -/

theorem chapter05_autocorrelation_fourier_eq_normSq
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (_hL2 : MemLp h 2 volume) (t : ℝ) :
    chapter05FourierTransform (chapter05Autocorrelation h) t =
      (Complex.normSq (chapter05FourierTransform h t) : ℂ) := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume := by
    refine ⟨continuous_neg.measurable, ?_⟩
    simpa only [neg_one_mul, abs_neg, abs_one, inv_neg, inv_one,
      ENNReal.ofReal_one, one_smul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  let hC : ℝ → ℂ := fun x => (h x : ℂ)
  let rC : ℝ → ℂ := fun x => (h (-x) : ℂ)
  have hCInt : Integrable hC volume := by
    change Integrable (fun x : ℝ => (h x : ℂ)) volume
    exact hL1.ofReal
  have hrCInt : Integrable rC volume := by
    have hr : Integrable (fun x : ℝ => h (-x)) volume := by
      simpa only [Function.comp_def] using hneg.integrable_comp_of_integrable hL1
    change Integrable (fun x : ℝ => (h (-x) : ℂ)) volume
    exact hr.ofReal
  have hconv (x : ℝ) :
      (chapter05Autocorrelation h x : ℂ) =
        (hC ⋆[ContinuousLinearMap.lsmul ℂ ℂ] rC) x := by
    unfold chapter05Autocorrelation chapter05Convolution chapter05Reflect
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hC, rC]
    simp_rw [← Complex.ofReal_mul]
    exact (integral_ofReal).symm
  have hReflectL1 : Integrable (chapter05Reflect h) volume := by
    unfold chapter05Reflect
    simpa only [Function.comp_def] using hneg.integrable_comp_of_integrable hL1
  have hAutoInt : Integrable (chapter05Autocorrelation h) volume := by
    change Integrable (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ] chapter05Reflect h) volume
    exact hL1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hReflectL1
  have hreflectFT :
      chapter05FourierTransform (chapter05Reflect h) t =
        conj (chapter05FourierTransform h t) := by
    unfold chapter05FourierTransform chapter05Reflect
    have hexp (x : ℝ) :
        Complex.exp (-(Complex.I * ((t * (-x) : ℝ) : ℂ))) =
          conj (Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) := by
      rw [← Complex.exp_conj]
      congr 1
      push_cast
      simp
    calc
      (∫ x : ℝ, (h (-x) : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume) =
          ∫ x : ℝ, (h x : ℂ) *
            Complex.exp (-(Complex.I * ((t * (-x) : ℝ) : ℂ))) ∂volume := by
        simpa only [Function.comp_def, neg_neg] using
          hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding
            (fun x : ℝ => (h x : ℂ) *
              Complex.exp (-(Complex.I * ((t * (-x) : ℝ) : ℂ))))
      _ = ∫ x : ℝ, conj ((h x : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [map_mul, Complex.conj_ofReal, hexp]
      _ = conj (∫ x : ℝ, (h x : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume) := by
        exact integral_conj
  have hconv_fun :
      (fun x : ℝ => (chapter05Autocorrelation h x : ℂ)) =
        hC ⋆[ContinuousLinearMap.lsmul ℂ ℂ] rC := funext hconv
  let ξ : ℝ := t / (2 * Real.pi)
  have hhFT : 𝓕 hC ξ = chapter05FourierTransform h t := by
    symm
    simpa only [ξ, hC] using
      (chapter05_fourierTransform_eq_mathlib_angular h hL1 t)
  have hrFT : 𝓕 rC ξ = conj (chapter05FourierTransform h t) := by
    calc
      𝓕 rC ξ = chapter05FourierTransform (chapter05Reflect h) t := by
        symm
        simpa only [ξ, rC, chapter05Reflect] using
          (chapter05_fourierTransform_eq_mathlib_angular
            (chapter05Reflect h) hReflectL1 t)
      _ = conj (chapter05FourierTransform h t) := hreflectFT
  have hAutoFT :
      chapter05FourierTransform (chapter05Autocorrelation h) t =
        𝓕 (fun x : ℝ => (chapter05Autocorrelation h x : ℂ)) ξ := by
    simpa only [ξ] using
      (chapter05_fourierTransform_eq_mathlib_angular
        (chapter05Autocorrelation h) hAutoInt t)
  have hConvFT := Real.fourier_smul_convolution_eq hCInt hrCInt ξ
  rw [hAutoFT, hconv_fun, hConvFT, hhFT, hrFT]
  simp only [smul_eq_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- The value at the origin is the squared `L²` mass of the input. -/
theorem chapter05_autocorrelation_apply_zero_eq_l2_sq
    (h : ℝ → ℝ) (_hL2 : MemLp h 2 volume) :
    chapter05Autocorrelation h 0 = ∫ x : ℝ, h x ^ 2 ∂volume := by
  unfold chapter05Autocorrelation chapter05Convolution chapter05Reflect
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, zero_sub, neg_neg]
  change (∫ x : ℝ, h x * h x ∂volume) = ∫ x : ℝ, h x ^ 2 ∂volume
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- Strict positivity requires nonvanishing modulo almost-everywhere equality. -/
theorem chapter05_autocorrelation_apply_zero_pos
    (h : ℝ → ℝ) (hL2 : MemLp h 2 volume)
    (hNeZero : ¬ h =ᵐ[volume] (0 : ℝ → ℝ)) :
    0 < chapter05Autocorrelation h 0 := by
  have hsq : Integrable (fun x : ℝ => h x ^ 2) volume := hL2.integrable_sq
  have hsq_ne : ¬ (fun x : ℝ => h x ^ 2) =ᵐ[volume] (0 : ℝ → ℝ) := by
    intro hs
    apply hNeZero
    filter_upwards [hs] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hne : (∫ x : ℝ, h x ^ 2 ∂volume) ≠ 0 := by
    intro hz
    apply hsq_ne
    exact (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (h x)) hsq).mp hz
  have hpos : 0 < ∫ x : ℝ, h x ^ 2 ∂volume :=
    lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (h x))) (Ne.symm hne)
  rw [chapter05_autocorrelation_apply_zero_eq_l2_sq h hL2]
  exact hpos

theorem chapter05_autocorrelation_is_even
    (h : ℝ → ℝ) (_hL1 : Integrable h volume) (_hL2 : MemLp h 2 volume) :
    Function.Even (chapter05Autocorrelation h) := by
  intro x
  unfold chapter05Autocorrelation chapter05Convolution chapter05Reflect
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  calc
    (∫ t : ℝ, h t * h (-(-x - t)) ∂volume) =
        ∫ t : ℝ, h t * h (t + x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with t
      congr 2
      ring
    _ =
        ∫ t : ℝ, h (t - x) * h t ∂volume := by
      rw [← integral_add_right_eq_self (fun t : ℝ => h (t - x) * h t) x]
      congr 1
      funext t
      ring_nf
    _ = ∫ t : ℝ, h t * h (-(x - t)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with t
      ring_nf

theorem chapter05_autocorrelation_is_positive_type
    (h : ℝ → ℝ) (hL1 : Integrable h volume) (hL2 : MemLp h 2 volume) :
    Chapter05PositiveType (chapter05Autocorrelation h) := by
  let hLp : Lp ℝ 2 volume := hL2.toLp h
  let g₀ : C(ℝ × ℝ, ℝ) :=
    ContinuousMap.mk (fun p : ℝ × ℝ => -p.1 + p.2) (by fun_prop)
  let g : ℝ → C(ℝ, ℝ) := g₀.curry
  have hg : Continuous g := by
    exact g₀.curry.continuous
  have hgm (x : ℝ) : MeasurePreserving (g x) volume volume := by
    change MeasurePreserving (fun y : ℝ => -x + y) volume volume
    simpa only [g, g₀, ContinuousMap.curry_apply] using
      (measurePreserving_add_left volume (-x))
  have htrans : Continuous
      (fun x : ℝ => Lp.compMeasurePreserving (g x) (hgm x) hLp) := by
    exact continuous_const.compMeasurePreservingLp hg hgm (by norm_num)
  have hcontInner : Continuous
      (fun x : ℝ => inner ℝ hLp (Lp.compMeasurePreserving (g x) (hgm x) hLp)) := by
    fun_prop
  have hEqInner (x : ℝ) :
      chapter05Autocorrelation h x =
        inner ℝ hLp (Lp.compMeasurePreserving (g x) (hgm x) hLp) := by
    unfold chapter05Autocorrelation chapter05Convolution chapter05Reflect
    rw [MeasureTheory.convolution_def, L2.inner_def]
    have hh : (fun a : ℝ => hLp a) =ᵐ[volume] h := by
      simpa [hLp] using hL2.coeFn_toLp
    have hhcomp : (fun a : ℝ => hLp (g x a)) =ᵐ[volume]
        (fun a : ℝ => h (g x a)) := by
      exact (hgm x).quasiMeasurePreserving.ae_eq_comp hh
    have hcomp := Lp.coeFn_compMeasurePreserving hLp (hgm x)
    apply integral_congr_ae
    filter_upwards [hh, hcomp, hhcomp] with a ha hcompa hacompa
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [ha, hcompa]
    dsimp only [Function.comp_apply]
    rw [hacompa]
    rw [Real.inner_apply]
    dsimp [g, g₀]
    congr 2
    ring
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume := by
    refine ⟨continuous_neg.measurable, ?_⟩
    simpa only [neg_one_mul, abs_neg, abs_one, inv_neg, inv_one,
      ENNReal.ofReal_one, one_smul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hReflectL1 : Integrable (chapter05Reflect h) volume := by
    unfold chapter05Reflect
    simpa only [Function.comp_def] using hneg.integrable_comp_of_integrable hL1
  have hAutoInt : Integrable (chapter05Autocorrelation h) volume := by
    change Integrable (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ] chapter05Reflect h) volume
    exact hL1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hReflectL1
  have hEven := chapter05_autocorrelation_is_even h hL1 hL2
  refine
    { continuous := hcontInner.congr (fun x => (hEqInner x).symm)
      integrable := hAutoInt
      transformNonnegative := ?_ }
  intro t
  have hReal := chapter05_fourier_transform_eq_ofReal_real_transform hAutoInt hEven t
  have hNorm := chapter05_autocorrelation_fourier_eq_normSq h hL1 hL2 t
  constructor
  · simpa using congrArg Complex.im hReal
  · rw [hNorm]
    exact Complex.normSq_nonneg _

theorem chapter05_positive_type_real_transform_nonnegative
    {G : ℝ → ℝ} (hG : Chapter05PositiveType G) :
    ∀ t : ℝ, 0 ≤ chapter05RealFourierTransform G t := by
  sorry

def chapter05StripKernel (a : ℝ) (x : ℝ) : ℝ :=
  Real.cosh (a * x) / Real.cosh (x / 2)

theorem chapter05_strip_kernel_endpoint (a x : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter05StripKernel a x = 1 := by
  sorry

theorem chapter05_strip_kernel_half (x : ℝ) :
    chapter05StripKernel (1 / 2 : ℝ) x = 1 := by
  sorry

theorem chapter05_strip_kernel_neg_half (x : ℝ) :
    chapter05StripKernel (-(1 / 2 : ℝ)) x = 1 := by
  sorry

theorem chapter05_strip_kernel_endpoint_product_reduces
    (G : ℝ → ℝ) (a : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    (fun x => G x * chapter05StripKernel a x) = G := by
  sorry

theorem chapter05_strip_kernel_fourier_closed_form (a t : ℝ)
    (ha : |a| < 1 / 2) :
    chapter05FourierTransform (chapter05StripKernel a) t =
      (4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a)) : ℂ) := by
  sorry

theorem chapter05_strip_kernel_positive_type (a : ℝ)
    (ha : |a| < 1 / 2) :
    Chapter05PositiveType (chapter05StripKernel a) := by
  sorry

theorem chapter05_positive_type_mul
    (f g : ℝ → ℝ)
    (hf : Chapter05PositiveType f) (hg : Chapter05PositiveType g) :
    Chapter05PositiveType (fun x => f x * g x) := by
  sorry

theorem chapter05_pair_kernel_positive_type_strict
    (G : ℝ → ℝ) (a : ℝ)
    (hG : Chapter05PositiveType G) (ha : |a| < 1 / 2) :
    Chapter05PositiveType
      (fun x : ℝ => G x * chapter05StripKernel a x) := by
  sorry

theorem chapter05_pair_kernel_positive_type_endpoint
    (G : ℝ → ℝ) (a : ℝ)
    (hG : Chapter05PositiveType G)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    Chapter05PositiveType
      (fun x : ℝ => G x * chapter05StripKernel a x) := by
  sorry

theorem chapter05_pair_kernel_positive_type
    (G : ℝ → ℝ) (a : ℝ)
    (hG : Chapter05PositiveType G) (ha : |a| ≤ 1 / 2) :
    Chapter05PositiveType
      (fun x : ℝ => G x * (Real.cosh (a * x) / Real.cosh (x / 2))) := by
  sorry

@[simp] theorem chapter05_normalizeAtZero_apply_zero
    (G : ℝ → ℝ) (hG0 : G 0 ≠ 0) :
    chapter05NormalizeAtZero G hG0 0 = 1 := by
  unfold chapter05NormalizeAtZero
  exact div_self hG0

theorem chapter05_positive_type_does_not_imply_pointwise_nonnegative :
    ∃ G : ℝ → ℝ, Chapter05PositiveType G ∧ ∃ x : ℝ, G x < 0 := by
  let A : Set ℝ := Set.Ioc 0 1
  let B : Set ℝ := Set.Ioc 1 2
  let u : ℝ → ℝ := fun _ => 1
  let h : ℝ → ℝ := A.indicator u - B.indicator u
  have hA1 : Integrable (A.indicator u) volume := by
    dsimp [A, u]
    exact (continuous_const.integrableOn_Ioc :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) volume).integrable_indicator
      measurableSet_Ioc
  have hB1 : Integrable (B.indicator u) volume := by
    dsimp [B, u]
    exact (continuous_const.integrableOn_Ioc :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 1 2) volume).integrable_indicator
      measurableSet_Ioc
  have hA2 : MemLp (A.indicator u) 2 volume := by
    dsimp [A, u]
    exact memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr measure_Ioc_lt_top.ne)
  have hB2 : MemLp (B.indicator u) 2 volume := by
    dsimp [B, u]
    exact memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr measure_Ioc_lt_top.ne)
  have hL1 : Integrable h volume := by
    change Integrable (A.indicator u - B.indicator u) volume
    exact hA1.sub hB1
  have hL2 : MemLp h 2 volume := by
    change MemLp (A.indicator u - B.indicator u) 2 volume
    exact hA2.sub hB2
  have hprod (t : ℝ) :
      h t * h (-(1 - t)) = -B.indicator u t := by
    have harg : -(1 - t) = t - 1 := by ring
    by_cases htB : t ∈ B
    · have htB' : 1 < t ∧ t ≤ 2 := by simpa [B] using htB
      have htA : t ∉ A := by
        intro htA
        have htA' : 0 < t ∧ t ≤ 1 := by simpa [A] using htA
        linarith
      have htshiftA : t - 1 ∈ A := by
        have htshiftA' : 0 < t - 1 ∧ t - 1 ≤ 1 := by
          constructor <;> linarith [htB'.1, htB'.2]
        simpa [A] using htshiftA'
      have htshiftB : t - 1 ∉ B := by
        intro htshiftB
        have htshiftB' : 1 < t - 1 ∧ t - 1 ≤ 2 := by simpa [B] using htshiftB
        linarith
      rw [harg]
      simp [h, u, htB, htA, htshiftA, htshiftB]
    · by_cases htA : t ∈ A
      · have htA' : 0 < t ∧ t ≤ 1 := by simpa [A] using htA
        have htshiftA : t - 1 ∉ A := by
          intro htshiftA
          have htshiftA' : 0 < t - 1 ∧ t - 1 ≤ 1 := by simpa [A] using htshiftA
          linarith
        have htshiftB : t - 1 ∉ B := by
          intro htshiftB
          have htshiftB' : 1 < t - 1 ∧ t - 1 ≤ 2 := by simpa [B] using htshiftB
          linarith
        rw [harg]
        simp [h, u, htB, htA, htshiftA, htshiftB]
      · simp [h, u, htB, htA]
  have hAuto : chapter05Autocorrelation h 1 = -1 := by
    unfold chapter05Autocorrelation chapter05Convolution chapter05Reflect
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    calc
      (∫ t : ℝ, h t * h (-(1 - t)) ∂volume) =
          ∫ t : ℝ, -B.indicator u t ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hprod t
      _ = -∫ t : ℝ, B.indicator u t ∂volume := by rw [integral_neg]
      _ = -1 := by
        rw [show B.indicator u = (Set.Ioc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) by rfl]
        rw [integral_indicator_const 1 measurableSet_Ioc]
        simp
        ring
  refine ⟨chapter05Autocorrelation h, chapter05_autocorrelation_is_positive_type h hL1 hL2,
    1, ?_⟩
  rw [hAuto]
  norm_num

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
