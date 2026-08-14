import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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
  intro t
  have hFTInt : Integrable
      (fun x : ℝ => (G x : ℂ) *
        Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) volume := by
    apply hG.integrable.ofReal.mul_bdd
    · exact (Complex.continuous_exp.comp
        ((continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).neg)).aestronglyMeasurable
    · filter_upwards [] with x
      change ‖Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))‖ ≤ 1
      rw [show -(Complex.I * ((t * x : ℝ) : ℂ)) =
          (((-(t * x) : ℝ) : ℂ) * Complex.I) by
            push_cast
            ring,
        Complex.norm_exp_ofReal_mul_I]
  have hRe :
      (chapter05FourierTransform G t).re =
        chapter05RealFourierTransform G t := by
    unfold chapter05FourierTransform chapter05RealFourierTransform
    calc
      (∫ x : ℝ, (G x : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume).re =
          ∫ x : ℝ, ((G x : ℂ) *
            Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))).re ∂volume :=
        (integral_re hFTInt).symm
      _ = ∫ x : ℝ, G x * Real.cos (t * x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hre : (Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))).re =
            Real.cos (t * x) := by
          rw [show -(Complex.I * ((t : ℂ) * (x : ℂ))) =
              (((-(t * x) : ℝ) : ℂ) * Complex.I) by
                push_cast
                ring]
          simpa only [Real.cos_neg] using Complex.exp_ofReal_mul_I_re (-(t * x))
        have him : (Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))).im =
            -Real.sin (t * x) := by
          rw [show -(Complex.I * ((t : ℂ) * (x : ℂ))) =
              (((-(t * x) : ℝ) : ℂ) * Complex.I) by
                push_cast
                ring]
          simpa only [Real.sin_neg] using Complex.exp_ofReal_mul_I_im (-(t * x))
        simp [Complex.mul_re, hre, him]
  have hnonneg := (hG.transformNonnegative t).2
  rw [hRe] at hnonneg
  exact hnonneg

def chapter05StripKernel (a : ℝ) (x : ℝ) : ℝ :=
  Real.cosh (a * x) / Real.cosh (x / 2)

theorem chapter05_strip_kernel_endpoint (a x : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter05StripKernel a x = 1 := by
  rcases ha with rfl | rfl <;> unfold chapter05StripKernel
  · rw [show (1 / 2 : ℝ) * x = x / 2 by ring]
    exact div_self (Real.cosh_pos _).ne'
  · rw [show (-(1 / 2 : ℝ)) * x = -(x / 2) by ring, Real.cosh_neg]
    exact div_self (Real.cosh_pos _).ne'

theorem chapter05_strip_kernel_half (x : ℝ) :
    chapter05StripKernel (1 / 2 : ℝ) x = 1 := by
  exact chapter05_strip_kernel_endpoint (1 / 2 : ℝ) x (Or.inl rfl)

theorem chapter05_strip_kernel_neg_half (x : ℝ) :
    chapter05StripKernel (-(1 / 2 : ℝ)) x = 1 := by
  exact chapter05_strip_kernel_endpoint (-(1 / 2 : ℝ)) x (Or.inr rfl)

theorem chapter05_strip_kernel_endpoint_product_reduces
    (G : ℝ → ℝ) (a : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    (fun x => G x * chapter05StripKernel a x) = G := by
  funext x
  rw [chapter05_strip_kernel_endpoint a x ha]
  simp

private theorem chapter05_strip_kernel_integrable (a : ℝ)
    (ha : |a| < 1 / 2) :
    Integrable (chapter05StripKernel a) volume := by
  let c : ℝ := 1 / 2 - |a|
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hright : IntegrableOn
      (fun x : ℝ => 2 * Real.exp (-c * x)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    change Integrable (fun x : ℝ => 2 * Real.exp (-c * x))
      (volume.restrict (Set.Ioi 0))
    exact (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul 2
  have hleft : IntegrableOn
      (fun x : ℝ => 2 * Real.exp (c * x)) (Set.Iic 0) := by
    change Integrable (fun x : ℝ => 2 * Real.exp (c * x))
      (volume.restrict (Set.Iic 0))
    exact (integrableOn_exp_mul_Iic (a := c) hc 0).const_mul 2
  have hcont : Continuous (chapter05StripKernel a) := by
    unfold chapter05StripKernel
    apply (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hright' : IntegrableOn (chapter05StripKernel a) (Set.Ici 0) := by
    apply Integrable.mono' hright
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx0 : 0 ≤ x := hx
      have hupper : Real.cosh (a * x) ≤ Real.exp (|a| * x) := by
        have hcosh : Real.cosh (a * x) ≤ Real.exp |a * x| := by
          rw [Real.cosh_eq]
          nlinarith [Real.exp_le_exp.mpr (le_abs_self (a * x)),
            Real.exp_le_exp.mpr (neg_le_abs (a * x))]
        apply hcosh.trans
        apply Real.exp_le_exp.mpr
        have habs : |a * x| = |a| * x := by
          calc
            |a * x| = |a| * |x| := abs_mul a x
            _ = |a| * x := congrArg (fun z : ℝ => |a| * z) (abs_of_nonneg hx0)
        exact habs.le
      have hlower : Real.exp (x / 2) / 2 ≤ Real.cosh (x / 2) := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (x / 2), Real.exp_pos (-(x / 2))]
      have hbound : Real.cosh (a * x) ≤
          2 * Real.exp (-c * x) * Real.cosh (x / 2) := by
        calc
          Real.cosh (a * x) ≤ Real.exp (|a| * x) := hupper
          _ = 2 * (Real.exp (-c * x) * (Real.exp (x / 2) / 2)) := by
            calc
              Real.exp (|a| * x) = Real.exp (-c * x) * Real.exp (x / 2) := by
                rw [← Real.exp_add]
                congr 1
                dsimp [c]
                ring
              _ = 2 * (Real.exp (-c * x) * (Real.exp (x / 2) / 2)) := by ring
          _ ≤ 2 * (Real.exp (-c * x) * Real.cosh (x / 2)) := by
            gcongr
          _ = 2 * Real.exp (-c * x) * Real.cosh (x / 2) := by ring
      unfold chapter05StripKernel
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le)]
      exact (div_le_iff₀ (Real.cosh_pos _)).2 hbound
  have hleft' : IntegrableOn (chapter05StripKernel a) (Set.Iic 0) := by
    apply Integrable.mono' hleft
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hx0 : x ≤ 0 := hx
      have hupper : Real.cosh (a * x) ≤ Real.exp (|a| * (-x)) := by
        have hcosh : Real.cosh (a * x) ≤ Real.exp |a * x| := by
          rw [Real.cosh_eq]
          nlinarith [Real.exp_le_exp.mpr (le_abs_self (a * x)),
            Real.exp_le_exp.mpr (neg_le_abs (a * x))]
        apply hcosh.trans
        apply Real.exp_le_exp.mpr
        have habs : |a * x| = |a| * (-x) := by
          calc
            |a * x| = |a| * |x| := abs_mul a x
            _ = |a| * (-x) :=
              congrArg (fun z : ℝ => |a| * z) (abs_of_nonpos hx0)
        exact habs.le
      have hlower : Real.exp (-(x / 2)) / 2 ≤ Real.cosh (x / 2) := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (x / 2), Real.exp_pos (-(x / 2))]
      have hbound : Real.cosh (a * x) ≤
          2 * Real.exp (c * x) * Real.cosh (x / 2) := by
        calc
          Real.cosh (a * x) ≤ Real.exp (|a| * (-x)) := hupper
          _ = 2 * (Real.exp (c * x) * (Real.exp (-(x / 2)) / 2)) := by
            calc
              Real.exp (|a| * (-x)) = Real.exp (c * x) *
                  Real.exp (-(x / 2)) := by
                rw [← Real.exp_add]
                congr 1
                dsimp [c]
                ring
              _ = 2 * (Real.exp (c * x) * (Real.exp (-(x / 2)) / 2)) := by ring
          _ ≤ 2 * (Real.exp (c * x) * Real.cosh (x / 2)) := by
            gcongr
          _ = 2 * Real.exp (c * x) * Real.cosh (x / 2) := by ring
      unfold chapter05StripKernel
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le)]
      exact (div_le_iff₀ (Real.cosh_pos _)).2 hbound
  rw [← integrableOn_univ, ← Set.Iic_union_Ici, integrableOn_union]
  exact ⟨hleft', hright'⟩

private theorem chapter05_integral_cpow_div_one_add
    (s : ℂ) :
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s - 1) / (1 + (y : ℂ))) =
      Complex.betaIntegral s (1 - s) := by
  let φ : ℝ → ℝ := fun x => x / (1 - x)
  have hφ_image : φ '' Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos hx.1 (sub_pos.mpr hx.2)
    · intro hy
      have hy' : 0 < y := hy
      refine ⟨y / (1 + y), ?_, ?_⟩
      · constructor
        · exact div_pos hy' (by linarith)
        · apply (div_lt_one (by linarith : 0 < 1 + y)).2
          linarith
      · have hy₀ : 1 + y ≠ 0 := by linarith
        dsimp [φ]
        field_simp [hy₀]
        ring
  have hφ_inj : Set.InjOn φ (Set.Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hx₀ : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
    have hy₀ : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy.2)
    dsimp [φ] at hxy
    field_simp [hx₀, hy₀] at hxy
    linarith
  have hφ_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt φ ((1 - x)⁻¹ ^ 2) (Set.Ioo (0 : ℝ) 1) x := by
    intro x hx
    have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1
      · rfl
      · rfl
      · funext y
        simp [id]
      · ring
    have h := (hasDerivAt_id x).div hden (by linarith [hx.2])
    convert h.hasDerivWithinAt using 1 <;> try rfl
    dsimp [id]
    field_simp [ne_of_gt (sub_pos.mpr hx.2)]
    ring
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul (F := ℂ) measurableSet_Ioo
      hφ_deriv hφ_inj (fun y : ℝ => (y : ℂ) ^ (s - 1) / (1 + (y : ℂ)))
  rw [hφ_image] at hchange
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  calc
    (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (s - 1) / (1 + (y : ℂ))) =
        ∫ x : ℝ in Set.Ioo 0 1,
          |(1 - x)⁻¹ ^ 2| •
            (((φ x : ℝ) : ℂ) ^ (s - 1) / (1 + ((φ x : ℝ) : ℂ))) := hchange
    _ = ∫ x : ℝ in Set.Ioo 0 1,
        (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((1 - s) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      change |(1 - x)⁻¹ ^ 2| •
          (((φ x : ℝ) : ℂ) ^ (s - 1) / (1 + ((φ x : ℝ) : ℂ))) =
        (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((1 - s) - 1)
      have hx₀ : 0 < x := hx.1
      have hx₁ : 0 < 1 - x := sub_pos.mpr hx.2
      have hxp : 0 ≤ (1 - x)⁻¹ ^ 2 := sq_nonneg _
      rw [abs_of_nonneg hxp, Complex.real_smul]
      have hpow :
          ((x / (1 - x) : ℝ) : ℂ) ^ (s - 1) =
            (x : ℂ) ^ (s - 1) / (1 - (x : ℂ)) ^ (s - 1) := by
        simpa [Complex.ofReal_div, Complex.ofReal_sub] using
          (Complex.div_cpow_ofReal_nonneg hx₀.le hx₁.le (s - 1))
      rw [hpow]
      have hden : (1 - x : ℝ) ≠ 0 := hx₁.ne'
      have hdenC : (1 - (x : ℂ)) ≠ 0 := by
        simpa [Complex.ofReal_sub] using (Complex.ofReal_ne_zero.mpr hden)
      have hsum :
          (1 : ℂ) + ((x / (1 - x) : ℝ) : ℂ) = (1 - (x : ℂ))⁻¹ := by
        rw [Complex.ofReal_div, Complex.ofReal_sub]
        field_simp [hdenC]
        norm_num
      rw [hsum]
      rw [div_inv_eq_mul]
      rw [show (((1 - x)⁻¹ ^ 2 : ℝ) : ℂ) = (1 - (x : ℂ))⁻¹ ^ 2 by
        norm_num]
      have hpowS : (1 - (x : ℂ)) ^ s ≠ 0 :=
        (Complex.cpow_ne_zero_iff).2 (Or.inl hdenC)
      rw [show (1 - s) - 1 = -s by ring, Complex.cpow_neg]
      rw [Complex.cpow_sub s 1 hdenC, Complex.cpow_one]
      field_simp [hdenC, hpowS]

private theorem chapter05_integral_exp_div_one_add (s : ℂ) :
    (∫ x : ℝ, Complex.exp (s * (x : ℂ)) /
      (1 + (Real.exp x : ℂ))) = Complex.betaIntegral s (1 - s) := by
  let ψ : ℝ → ℝ := fun x => Real.exp x
  have hψ_image : ψ '' Set.univ = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact Real.exp_pos x
    · intro hy
      refine ⟨Real.log y, Set.mem_univ _, ?_⟩
      exact Real.exp_log hy
  have hψ_inj : Set.InjOn ψ Set.univ := by
    intro x _ y _ hxy
    exact Real.exp_injective hxy
  have hψ_deriv : ∀ x ∈ Set.univ,
      HasDerivWithinAt ψ (Real.exp x) Set.univ x := by
    intro x _
    exact (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul (F := ℂ) MeasurableSet.univ
      hψ_deriv hψ_inj
        (fun y : ℝ => (y : ℂ) ^ (s - 1) / (1 + (y : ℂ)))
  rw [hψ_image] at hchange
  calc
    (∫ x : ℝ, Complex.exp (s * (x : ℂ)) /
        (1 + (Real.exp x : ℂ))) =
        ∫ x : ℝ, |Real.exp x| •
          (((Real.exp x : ℂ) ^ (s - 1)) /
            (1 + (Real.exp x : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_of_pos (Real.exp_pos x), Complex.real_smul]
      have hexp : (Real.exp x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
      have hcpow :
          (Real.exp x : ℂ) ^ (s - 1) =
            Complex.exp ((s - 1) * (x : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hexp]
        rw [← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
        congr 1
        ring
      rw [hcpow, Complex.ofReal_exp]
      have hden : (1 + (Real.exp x : ℂ)) ≠ 0 := by
        have hden' :
            1 + (Real.exp x : ℂ) = ((1 + Real.exp x : ℝ) : ℂ) := by
          norm_num
        rw [hden']
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      field_simp [hden]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    _ = ∫ y : ℝ in Set.Ioi 0,
        (y : ℂ) ^ (s - 1) / (1 + (y : ℂ)) := by
      simpa [ψ] using hchange.symm
    _ = Complex.betaIntegral s (1 - s) :=
      chapter05_integral_cpow_div_one_add s

theorem chapter05_strip_kernel_fourier_closed_form (a t : ℝ)
    (ha : |a| < 1 / 2) :
    chapter05FourierTransform (chapter05StripKernel a) t =
      (4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a)) : ℂ) := by
  have hweighted : ∀ b : ℝ, |b| < 1 / 2 →
      Integrable (fun x : ℝ =>
        Real.exp (b * x) * (1 / Real.cosh (x / 2))) volume := by
    intro b hb
    have hstrip := chapter05_strip_kernel_integrable b hb
    have hcont : Continuous (fun x : ℝ =>
        Real.exp (b * x) * (1 / Real.cosh (x / 2))) := by
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
        ((continuous_const.div
          (Real.continuous_cosh.comp (continuous_id.div_const 2)))
          (fun x => (Real.cosh_pos _).ne'))
    apply Integrable.mono' (hstrip.const_mul 2)
    · exact hcont.aestronglyMeasurable
    · filter_upwards [] with x
      have hsech : 0 ≤ 1 / Real.cosh (x / 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le hsech)]
      calc
        Real.exp (b * x) * (1 / Real.cosh (x / 2)) ≤
            (Real.exp (b * x) + Real.exp (-b * x)) *
              (1 / Real.cosh (x / 2)) := by
          gcongr
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        _ = 2 * chapter05StripKernel b x := by
          unfold chapter05StripKernel
          rw [Real.cosh_eq]
          have hden :
              Real.exp (x * (1 / 2)) * (1 / 2) +
                Real.exp (x * (-1 / 2)) * (1 / 2) ≠ 0 := by
            positivity
          rw [Real.cosh_eq]
          field_simp [hden]
  let q : ℝ → ℝ → ℂ := fun b x =>
    ((Real.exp (b * x) * (1 / Real.cosh (x / 2)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))
  have hq : ∀ b : ℝ, |b| < 1 / 2 → Integrable (q b) volume := by
    intro b hb
    have hbase : Integrable (fun x : ℝ =>
        ((Real.exp (b * x) * (1 / Real.cosh (x / 2)) : ℝ) : ℂ)) volume :=
      (hweighted b hb).ofReal
    have hphase : AEStronglyMeasurable (fun x : ℝ =>
        Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) volume := by
      exact (Continuous.aestronglyMeasurable (by fun_prop))
    have hphase_bound : ∀ᵐ x : ℝ ∂volume,
        ‖Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))‖ ≤ 1 := by
      filter_upwards [] with x
      rw [show -(Complex.I * ((t * x : ℝ) : ℂ)) =
        (((-(t * x) : ℝ) : ℂ) * Complex.I) by
          push_cast
          ring,
        Complex.norm_exp_ofReal_mul_I]
    have hmul := hbase.mul_bdd hphase hphase_bound
    simpa [q] using hmul
  have hq_beta : ∀ b : ℝ, |b| < 1 / 2 →
      (1 / 2 : ℂ) * ∫ x : ℝ, q b x =
        Complex.betaIntegral
          (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))
          (1 - (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))) := by
    intro b hb
    let s : ℂ := ((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ)
    have hs := chapter05_integral_exp_div_one_add s
    have hreal : ∀ x : ℝ,
        (1 / 2 : ℝ) *
            (Real.exp (b * x) * (1 / Real.cosh (x / 2))) =
          Real.exp ((1 / 2 + b) * x) / (1 + Real.exp x) := by
      intro x
      rw [Real.cosh_eq]
      have hden :
          Real.exp (x * (1 / 2)) * (1 / 2) +
              Real.exp (x * (-1 / 2)) * (1 / 2) ≠ 0 := by
        positivity
      field_simp [hden]
      calc
        Real.exp (b * x) * (1 + Real.exp x) =
            Real.exp (b * x) + Real.exp (b * x + x) := by
          rw [mul_add, mul_one, ← Real.exp_add]
        _ = Real.exp (x / 2 + x * (1 + 2 * b) / 2) +
            Real.exp (-(x / 2) + x * (1 + 2 * b) / 2) := by
          have h₁ : x / 2 + x * (1 + 2 * b) / 2 = b * x + x := by
            ring
          have h₂ : -(x / 2) + x * (1 + 2 * b) / 2 = b * x := by ring
          rw [h₁, h₂]
          ring
        _ = (Real.exp (x / 2) + Real.exp (-(x / 2))) *
            Real.exp (x * (1 + 2 * b) / 2) := by
          rw [Real.exp_add, Real.exp_add, ← add_mul]
    calc
      (1 / 2 : ℂ) * ∫ x : ℝ, q b x =
          ∫ x : ℝ, (1 / 2 : ℂ) * q b x := by
        rw [integral_const_mul]
      _ = ∫ x : ℝ,
          Complex.exp (s * (x : ℂ)) /
            (1 + (Real.exp x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [q, s]
        calc
          (1 / 2 : ℂ) *
              (((Real.exp (b * x) * (1 / Real.cosh (x / 2)) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) =
              (((1 / 2 : ℝ) *
                (Real.exp (b * x) * (1 / Real.cosh (x / 2))) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) := by
            norm_num
            ring
          _ = (((Real.exp ((1 / 2 + b) * x) /
              (1 + Real.exp x) : ℝ) : ℂ) *
                Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) := by
            rw [hreal x]
          _ = Complex.exp (s * (x : ℂ)) /
              (1 + (Real.exp x : ℂ)) := by
            rw [Complex.ofReal_div, Complex.ofReal_exp]
            have hden : (1 + (Real.exp x : ℂ)) ≠ 0 := by
              have hden' : 1 + (Real.exp x : ℂ) =
                  ((1 + Real.exp x : ℝ) : ℂ) := by norm_num
              rw [hden']
              exact Complex.ofReal_ne_zero.mpr (by positivity)
            field_simp [hden]
            rw [← Complex.exp_add]
            have hden' : ((1 + Real.exp x : ℝ) : ℂ) =
                1 + (Real.exp x : ℂ) := by norm_num
            rw [hden']
            rw [mul_div_cancel_right₀ _ hden]
            congr 1
            dsimp [s]
            push_cast
            ring
      _ = Complex.betaIntegral s (1 - s) := hs
      _ = Complex.betaIntegral
          (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))
          (1 - (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))) := by
        rfl
  have hminus : |(-a : ℝ)| < 1 / 2 := by simpa [abs_neg] using ha
  have hbeta : ∀ b : ℝ, |b| < 1 / 2 →
      Complex.betaIntegral
          (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))
          (1 - (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))) =
        Real.pi /
          Complex.sin (Real.pi *
            (((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ))) := by
    intro b hb
    let s : ℂ := ((1 / 2 + b : ℝ) : ℂ) - Complex.I * (t : ℂ)
    have hs : 0 < s.re := by
      dsimp [s]
      norm_num [Complex.mul_re]
      linarith [((abs_lt.mp hb).1)]
    have hs' : 0 < (1 - s).re := by
      dsimp [s]
      norm_num [Complex.mul_re]
      linarith [((abs_lt.mp hb).2)]
    rw [Complex.betaIntegral_eq_Gamma_mul_div s (1 - s) hs hs']
    have hsum : s + (1 - s) = 1 := by ring
    rw [hsum, Complex.Gamma_one, div_one]
    exact Complex.Gamma_mul_Gamma_one_sub s
  have hfourier_beta :
      chapter05FourierTransform (chapter05StripKernel a) t =
        Complex.betaIntegral
            (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))
            (1 - (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))) +
          Complex.betaIntegral
            (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))
            (1 - (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))) := by
    have hqa := hq a ha
    have hqminus := hq (-a) hminus
    calc
      chapter05FourierTransform (chapter05StripKernel a) t =
          ∫ x : ℝ, (1 / 2 : ℂ) * (q a x + q (-a) x) := by
        unfold chapter05FourierTransform
        apply integral_congr_ae
        filter_upwards [] with x
        have hkernel : chapter05StripKernel a x =
            (Real.exp (a * x) + Real.exp (-a * x)) / 2 *
              (1 / Real.cosh (x / 2)) := by
          unfold chapter05StripKernel
          rw [Real.cosh_eq]
          have hden :
              Real.exp (x * (1 / 2)) * (1 / 2) +
                  Real.exp (x * (-1 / 2)) * (1 / 2) ≠ 0 := by
            positivity
          field_simp [hden]
        rw [hkernel]
        dsimp [q]
        push_cast
        ring
      _ = (1 / 2 : ℂ) * (∫ x : ℝ, q a x) +
          (1 / 2 : ℂ) * (∫ x : ℝ, q (-a) x) := by
        rw [integral_const_mul, integral_add hqa hqminus]
        ring
      _ = Complex.betaIntegral
            (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))
            (1 - (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))) +
          Complex.betaIntegral
            (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))
            (1 - (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))) := by
        rw [hq_beta a ha, hq_beta (-a) hminus]
  have hsinplus :
      Complex.sin (Real.pi *
          (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))) =
        ((Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) : ℝ) : ℂ) +
          ((Real.sin (Real.pi * a) * Real.sinh (Real.pi * t) : ℝ) : ℂ) *
            Complex.I := by
    have harg :
        (Real.pi : ℂ) *
            (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ)) =
          (((Real.pi * a : ℝ) : ℂ) -
            ((Real.pi * t : ℝ) : ℂ) * Complex.I) +
            (Real.pi / 2 : ℂ) := by
      norm_num
      ring
    rw [harg, Complex.sin_add_pi_div_two, Complex.cos_sub,
      Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_sinh]
    norm_num
    ring
  have hsinminus :
      Complex.sin (Real.pi *
          (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))) =
        ((Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) : ℝ) : ℂ) -
          ((Real.sin (Real.pi * a) * Real.sinh (Real.pi * t) : ℝ) : ℂ) *
            Complex.I := by
    have harg :
        (Real.pi : ℂ) *
            (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ)) =
          (-(((Real.pi * a : ℝ) : ℂ) +
            ((Real.pi * t : ℝ) : ℂ) * Complex.I)) +
            (Real.pi / 2 : ℂ) := by
      norm_num
      ring
    rw [harg, Complex.sin_add_pi_div_two, Complex.cos_neg,
      Complex.cos_add_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_sinh]
    norm_num
  rw [hfourier_beta, hbeta a ha, hbeta (-a) hminus]
  have hcos : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos, (abs_lt.mp ha).1,
      (abs_lt.mp ha).2]
  have hplus_ne :
      Complex.sin (Real.pi *
          (((1 / 2 + a : ℝ) : ℂ) - Complex.I * (t : ℂ))) ≠ 0 := by
    rw [hsinplus]
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) :=
      mul_pos hcos (Real.cosh_pos _)
    have hreal' : Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) = 0 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.zero_re] using hreal
    exact (ne_of_gt hpos) hreal'
  have hminus_ne :
      Complex.sin (Real.pi *
          (((1 / 2 + (-a : ℝ) : ℝ) : ℂ) - Complex.I * (t : ℂ))) ≠ 0 := by
    rw [hsinminus]
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) :=
      mul_pos hcos (Real.cosh_pos _)
    have hreal' : Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) = 0 := by
      simpa only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.zero_re] using hreal
    exact (ne_of_gt hpos) hreal'
  have hden : 0 <
      Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) := by
    have htrig := Real.sin_sq_add_cos_sq (Real.pi * a)
    have hhyper := Real.cosh_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
      Real.cosh_two_mul, show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
      Real.cos_two_mul]
    nlinarith [htrig, hhyper, sq_nonneg (Real.sinh (Real.pi * t)),
      sq_pos_of_pos hcos]
  have hden_cast :
      (Real.cosh (2 * Real.pi * t) : ℂ) +
          (Real.cos (2 * Real.pi * a) : ℂ) =
        ((Real.cosh (2 * Real.pi * t) +
            Real.cos (2 * Real.pi * a) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
  have hden_complex :
      (Real.cosh (2 * Real.pi * t) : ℂ) +
          (Real.cos (2 * Real.pi * a) : ℂ) ≠ 0 := by
    rw [hden_cast]
    exact Complex.ofReal_ne_zero.mpr hden.ne'
  have hplus_ne' :
      ((Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) : ℝ) : ℂ) +
          ((Real.sin (Real.pi * a) * Real.sinh (Real.pi * t) : ℝ) : ℂ) *
            Complex.I ≠ 0 := by
    rw [← hsinplus]
    exact hplus_ne
  have hminus_ne' :
      ((Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) : ℝ) : ℂ) -
          ((Real.sin (Real.pi * a) * Real.sinh (Real.pi * t) : ℝ) : ℂ) *
            Complex.I ≠ 0 := by
    rw [← hsinminus]
    exact hminus_ne
  have hden' : 0 <
      Real.cosh (Real.pi * t * 2) + Real.cos (Real.pi * a * 2) := by
    rw [show Real.pi * t * 2 = 2 * (Real.pi * t) by ring,
      show Real.pi * a * 2 = 2 * (Real.pi * a) by ring,
      Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * a),
      Real.cosh_sq (Real.pi * t), sq_nonneg (Real.sinh (Real.pi * t)),
      sq_pos_of_pos hcos]
  have hden_cast' :
      (Real.cosh (Real.pi * t * 2) : ℂ) +
          (Real.cos (Real.pi * a * 2) : ℂ) =
        ((Real.cosh (Real.pi * t * 2) +
            Real.cos (Real.pi * a * 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
  have hden_complex' :
      (Real.cosh (Real.pi * t * 2) : ℂ) +
          (Real.cos (Real.pi * a * 2) : ℂ) ≠ 0 := by
    rw [hden_cast']
    exact Complex.ofReal_ne_zero.mpr hden'.ne'
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * a)
  have hhyper := Real.cosh_sq (Real.pi * t)
  have hsquare : Real.sin (Real.pi * a) ^ 2 =
      1 - Real.cos (Real.pi * a) ^ 2 := by
    nlinarith [htrig]
  have hden_real :
      Real.cosh (Real.pi * t * 2) + Real.cos (Real.pi * a * 2) =
        2 * (Real.sinh (Real.pi * t) ^ 2 +
          Real.cos (Real.pi * a) ^ 2) := by
    rw [show Real.pi * t * 2 = 2 * (Real.pi * t) by ring,
      show Real.pi * a * 2 = 2 * (Real.pi * a) by ring,
      Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [htrig, hhyper]
  have hsum :
      Real.sinh (Real.pi * t) ^ 2 + Real.cos (Real.pi * a) ^ 2 =
        (Real.cos (Real.pi * a) * Real.cosh (Real.pi * t)) ^ 2 +
          (Real.sin (Real.pi * a) * Real.sinh (Real.pi * t)) ^ 2 := by
    calc
      Real.sinh (Real.pi * t) ^ 2 + Real.cos (Real.pi * a) ^ 2 =
          Real.cos (Real.pi * a) ^ 2 *
              (Real.sinh (Real.pi * t) ^ 2 + 1) +
            (1 - Real.cos (Real.pi * a) ^ 2) *
              Real.sinh (Real.pi * t) ^ 2 := by ring
      _ = Real.cos (Real.pi * a) ^ 2 * Real.cosh (Real.pi * t) ^ 2 +
            Real.sin (Real.pi * a) ^ 2 * Real.sinh (Real.pi * t) ^ 2 := by
          rw [← hhyper, ← hsquare]
      _ = (Real.cos (Real.pi * a) * Real.cosh (Real.pi * t)) ^ 2 +
            (Real.sin (Real.pi * a) * Real.sinh (Real.pi * t)) ^ 2 := by ring
  have hden_explicit :
      (Real.cosh (Real.pi * t * 2) : ℂ) +
          (Real.cos (Real.pi * a * 2) : ℂ) =
        ((2 * ((Real.cos (Real.pi * a) * Real.cosh (Real.pi * t)) ^ 2 +
          (Real.sin (Real.pi * a) * Real.sinh (Real.pi * t)) ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, hden_real, hsum]
  rw [hsinplus, hsinminus]
  field_simp [hplus_ne', hminus_ne', hden_complex']
  rw [hden_explicit]
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
  norm_num
  ring
  
theorem chapter05_strip_kernel_positive_type (a : ℝ)
    (ha : |a| < 1 / 2) :
    Chapter05PositiveType (chapter05StripKernel a) := by
  have hcont : Continuous (chapter05StripKernel a) := by
    unfold chapter05StripKernel
    apply (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hcos : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos, (abs_lt.mp ha).1, (abs_lt.mp ha).2]
  have hden : ∀ t : ℝ,
      0 < Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) := by
    intro t
    have htrig := Real.sin_sq_add_cos_sq (Real.pi * a)
    have hhyper := Real.cosh_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
      Real.cosh_two_mul, show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
      Real.cos_two_mul]
    nlinarith [htrig, hhyper, sq_nonneg (Real.sinh (Real.pi * t)),
      sq_pos_of_pos hcos]
  refine
    { continuous := hcont
      integrable := chapter05_strip_kernel_integrable a ha
      transformNonnegative := ?_ }
  intro t
  rw [chapter05_strip_kernel_fourier_closed_form a t ha]
  have hcast :
      4 * (Real.pi : ℂ) * (Real.cos (Real.pi * a) : ℂ) *
          (Real.cosh (Real.pi * t) : ℂ) /
        ((Real.cosh (2 * Real.pi * t) : ℂ) +
          (Real.cos (2 * Real.pi * a) : ℂ)) =
      (((4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a))) : ℝ) : ℂ) := by
    norm_num
  rw [hcast]
  constructor
  · rfl
  · change 0 ≤
      4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a))
    exact div_nonneg (by positivity) (hden t).le

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
  exact chapter05_positive_type_mul G (chapter05StripKernel a) hG
    (chapter05_strip_kernel_positive_type a ha)

theorem chapter05_pair_kernel_positive_type_endpoint
    (G : ℝ → ℝ) (a : ℝ)
    (hG : Chapter05PositiveType G)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    Chapter05PositiveType
      (fun x : ℝ => G x * chapter05StripKernel a x) := by
  rw [chapter05_strip_kernel_endpoint_product_reduces G a ha]
  exact hG

theorem chapter05_pair_kernel_positive_type
    (G : ℝ → ℝ) (a : ℝ)
    (hG : Chapter05PositiveType G) (ha : |a| ≤ 1 / 2) :
    Chapter05PositiveType
      (fun x : ℝ => G x * (Real.cosh (a * x) / Real.cosh (x / 2))) := by
  by_cases hstrict : |a| < 1 / 2
  · exact chapter05_pair_kernel_positive_type_strict G a hG hstrict
  · have hboundary : |a| = 1 / 2 := le_antisymm ha (le_of_not_gt hstrict)
    have ha' : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ) := by
      exact eq_or_eq_neg_of_abs_eq hboundary
    exact chapter05_pair_kernel_positive_type_endpoint G a hG ha'

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
