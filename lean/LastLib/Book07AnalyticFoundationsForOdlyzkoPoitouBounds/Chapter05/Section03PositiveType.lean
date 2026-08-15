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
open Filter
open scoped Topology Convolution FourierTransform ComplexConjugate RealInnerProductSpace

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
  have htest : ∀ (c v : ℝ), 0 < c →
      𝓕 (fun ξ : ℝ => Complex.exp
        (-(c⁻¹ : ℂ) * (‖ξ‖ ^ 2 : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫ : ℂ))) =
        (fun x : ℝ =>
          ((Real.pi : ℂ) / (c⁻¹ : ℂ)) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
            Complex.exp (-((Real.pi : ℂ) ^ 2) * (‖v - x‖ ^ 2 : ℂ) /
              (c⁻¹ : ℂ))) := by
    intro c v hc
    funext x
    have h := fourier_gaussian_innerProductSpace'
      (V := ℝ) (b := (c⁻¹ : ℂ)) (by simpa using (inv_pos.mpr hc)) v x
    simpa only using h
  have hbounded : ∀ (F : ℝ → ℝ) (hF : Chapter05PositiveType F),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖F x‖ ≤ C := by
    intro F hF
    let FC : ℝ → ℂ := fun x => (F x : ℂ)
    have hFC : Integrable FC volume := by
      change Integrable (fun x : ℝ => (F x : ℂ)) volume
      exact hF.integrable.ofReal
    have hFT_nonneg (ξ : ℝ) :
        (𝓕 FC ξ).im = 0 ∧ 0 ≤ (𝓕 FC ξ).re := by
      have hscale := hF.transformNonnegative (2 * Real.pi * ξ)
      have hmath := chapter05_fourierTransform_eq_mathlib_angular F hF.integrable
        (2 * Real.pi * ξ)
      have heq : 𝓕 FC ξ = chapter05FourierTransform F (2 * Real.pi * ξ) := by
        rw [hmath]
        simp only [FC]
        field_simp [Real.pi_ne_zero]
      rw [heq]
      exact hscale
    let C₀ : ℝ := ∫ x : ℝ, ‖FC x‖ ∂volume
    have hC₀ : 0 ≤ C₀ := by
      dsimp [C₀]
      exact integral_nonneg (fun x : ℝ => norm_nonneg (FC x))
    have hFT_bound (ξ : ℝ) : ‖𝓕 FC ξ‖ ≤ C₀ := by
      dsimp [C₀]
      rw [Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans
      simp_rw [Circle.norm_smul]
      rfl
    let q : ℝ → ℝ → ℝ → ℂ := fun c v ξ =>
      Complex.exp (-(c⁻¹ : ℂ) * (‖ξ‖ ^ 2 : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫ : ℂ))
    let K : ℝ → ℝ → ℝ → ℂ := fun c v x =>
      ((Real.pi : ℂ) / (c⁻¹ : ℂ)) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2) * (‖v - x‖ ^ 2 : ℂ) /
          (c⁻¹ : ℂ))
    have hqFT (c v : ℝ) (hc : 0 < c) : 𝓕 (q c v) = K c v := by
      simpa [q, K] using htest c v hc
    have hqInt (c v : ℝ) (hc : 0 < c) : Integrable (q c v) volume := by
      simpa [q] using
        (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
          (V := ℝ) (b := (c⁻¹ : ℂ))
          (by simpa using (inv_pos.mpr hc)) (2 * Real.pi * Complex.I) v)
    have hreg (c v : ℝ) (hc : 0 < c) :
        (∫ x : ℝ, K c v x • FC x ∂volume) =
          ∫ ξ : ℝ, q c v ξ • 𝓕 FC ξ ∂volume := by
      have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) (e := 𝐞) (μ := volume) (ν := volume)
        Real.continuous_fourierChar continuous_inner (hqInt c v hc) hFC
      rw [← hqFT c v hc]
      change
        (∫ x : ℝ,
            VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (q c v) x • FC x) =
          ∫ ξ : ℝ,
            q c v ξ • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) FC ξ
      simpa using hswap
    have hK_gaussian (c v x : ℝ) (hc : 0 < c) :
        K c v x =
          (Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
            Complex.exp (-((Real.pi : ℂ) ^ 2) * (c : ℂ) *
              (‖v - x‖ ^ 2 : ℂ)) := by
      dsimp [K]
      have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
      have hpow : (Real.pi : ℂ) / (c⁻¹ : ℂ) = (Real.pi * c : ℂ) := by
        field_simp
      rw [hpow]
      congr 2
      field_simp
    have hq_norm (c v ξ : ℝ) (hc : 0 < c) :
        ‖q c v ξ‖ = Real.exp (-(c⁻¹) * ‖ξ‖ ^ 2) := by
      dsimp [q]
      rw [Complex.norm_exp]
      norm_num [Complex.mul_re, sq_abs]
      left
      rw [← Complex.ofReal_pow]
      simp only [Complex.ofReal_re]
      exact sq_abs ξ
    have hq_zero (c ξ : ℝ) :
        q c 0 ξ = (Real.exp (-(c⁻¹) * ‖ξ‖ ^ 2) : ℂ) := by
      dsimp [q]
      rw [Complex.ofReal_exp]
      congr 1
      norm_num [Complex.mul_re, Complex.mul_im, sq_abs]
      left
      rw [← Complex.ofReal_pow]
      norm_cast
      exact sq_abs ξ
    have hFC_cont : Continuous FC := by
      exact Complex.continuous_ofReal.comp hF.continuous
    have hFT_cont : Continuous (𝓕 FC) := by
      change Continuous
        (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) FC)
      exact VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar continuous_inner hFC
    have hqFTInt (c v : ℝ) (hc : 0 < c) :
        Integrable (fun ξ : ℝ => q c v ξ • 𝓕 FC ξ) volume := by
      simpa only [smul_eq_mul] using
        (hqInt c v hc).mul_bdd hFT_cont.aestronglyMeasurable
          (Filter.Eventually.of_forall hFT_bound)
    have hFT_real (ξ : ℝ) :
        𝓕 FC ξ = ((𝓕 FC ξ).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simp [hFT_nonneg ξ |>.1]
    have hnorm_FT (ξ : ℝ) :
        ‖𝓕 FC ξ‖ = (𝓕 FC ξ).re := by
      rw [hFT_real ξ]
      simp [Real.norm_of_nonneg (hFT_nonneg ξ).2]
    have hq_zero_mul (c ξ : ℝ) :
        q c 0 ξ • 𝓕 FC ξ =
          ((Real.exp (-(c⁻¹) * ‖ξ‖ ^ 2) * (𝓕 FC ξ).re : ℝ) : ℂ) := by
      rw [hq_zero c ξ, hFT_real ξ]
      simp [smul_eq_mul, Complex.ofReal_mul]
    have hnorm_integrand (c v ξ : ℝ) (hc : 0 < c) :
        ‖q c v ξ • 𝓕 FC ξ‖ = (q c 0 ξ • 𝓕 FC ξ).re := by
      rw [norm_smul, hq_norm c v ξ hc, hnorm_FT ξ, hq_zero_mul]
      simp only [Complex.ofReal_re]
    let D : ℝ → ℝ := fun c =>
      (∫ ξ : ℝ, q c 0 ξ • 𝓕 FC ξ ∂volume).re
    have hD_eq (c : ℝ) (hc : 0 < c) :
        D c = ∫ ξ : ℝ, (q c 0 ξ • 𝓕 FC ξ).re ∂volume := by
      dsimp [D]
      exact (integral_re (hqFTInt c 0 hc)).symm
    have hD_nonneg (c : ℝ) (hc : 0 < c) : 0 ≤ D c := by
      rw [hD_eq c hc]
      apply integral_nonneg
      change ∀ ξ : ℝ, 0 ≤ (q c 0 ξ • 𝓕 FC ξ).re
      intro ξ
      rw [hq_zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (hFT_nonneg ξ).2
    have hnorm_integral (c v : ℝ) (hc : 0 < c) :
        ∫ ξ : ℝ, ‖q c v ξ • 𝓕 FC ξ‖ ∂volume = D c := by
      calc
        (∫ ξ : ℝ, ‖q c v ξ • 𝓕 FC ξ‖ ∂volume) =
            ∫ ξ : ℝ, (q c 0 ξ • 𝓕 FC ξ).re ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ξ => hnorm_integrand c v ξ hc)
        _ = D c := (hD_eq c hc).symm
    have hleft_limit (v : ℝ) :
        Tendsto (fun c : ℝ => ∫ x : ℝ, K c v x • FC x ∂volume)
          atTop (𝓝 (FC v)) := by
      have h := Real.tendsto_integral_gaussian_smul' hFC
        (v := v) hFC_cont.continuousAt
      apply h.congr'
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change
          ((Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
            Complex.exp (-((Real.pi : ℂ) ^ 2) * (c : ℂ) *
              (‖v - x‖ ^ 2 : ℂ))) • FC x = K c v x • FC x
        rw [hK_gaussian c v x hc])
    have hD_limit : Tendsto D atTop (𝓝 (FC 0).re) := by
      have hleft0 := hleft_limit 0
      have hleft0_re :
          Tendsto (fun c : ℝ =>
            (∫ x : ℝ, K c 0 x • FC x ∂volume).re) atTop
            (𝓝 (FC 0).re) := by
        exact (Complex.continuous_re.tendsto (FC 0)).comp hleft0
      apply hleft0_re.congr'
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      rw [hreg c 0 hc]
    have hglobal (v : ℝ) : ‖FC v‖ ≤ (FC 0).re := by
      have hleft := hleft_limit v
      have hleft_norm :
          Tendsto (fun c : ℝ => ‖∫ x : ℝ, K c v x • FC x ∂volume‖)
            atTop (𝓝 ‖FC v‖) := by
        exact (continuous_norm.tendsto (FC v)).comp hleft
      apply le_of_tendsto_of_tendsto hleft_norm hD_limit
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      calc
        ‖∫ x : ℝ, K c v x • FC x ∂volume‖ =
            ‖∫ ξ : ℝ, q c v ξ • 𝓕 FC ξ ∂volume‖ := by
              rw [hreg c v hc]
        _ ≤ ∫ ξ : ℝ, ‖q c v ξ • 𝓕 FC ξ‖ ∂volume :=
          norm_integral_le_integral_norm _
        _ = D c := hnorm_integral c v hc
    refine ⟨(FC 0).re, ?_, ?_⟩
    · exact (norm_nonneg (FC 0)).trans (hglobal 0)
    intro x
    simpa [FC] using hglobal x
  obtain ⟨Cf, hCf, hfb⟩ := hbounded f hf
  obtain ⟨Cg, hCg, hgb⟩ := hbounded g hg
  have hfg_int : Integrable (fun x : ℝ => f x * g x) volume := by
    exact hf.integrable.mul_bdd hg.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hgb)
  have hfg_cont : Continuous (fun x : ℝ => f x * g x) :=
    hf.continuous.mul hg.continuous
  let FC : ℝ → ℂ := fun x => (f x : ℂ)
  let GC : ℝ → ℂ := fun x => (g x : ℂ)
  let HC : ℝ → ℂ := fun x => (f x * g x : ℂ)
  have hFC : Integrable FC volume := by
    change Integrable (fun x : ℝ => (f x : ℂ)) volume
    exact hf.integrable.ofReal
  have hGC : Integrable GC volume := by
    change Integrable (fun x : ℝ => (g x : ℂ)) volume
    exact hg.integrable.ofReal
  have hHC : Integrable HC volume := by
    dsimp [HC]
    exact hFC.mul_bdd (Complex.continuous_ofReal.comp hg.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa [GC] using hgb x))
  have hFC_cont : Continuous FC := Complex.continuous_ofReal.comp hf.continuous
  have hGC_cont : Continuous GC := Complex.continuous_ofReal.comp hg.continuous
  have hFT_F_nonneg (ξ : ℝ) :
      (𝓕 FC ξ).im = 0 ∧ 0 ≤ (𝓕 FC ξ).re := by
    have hscale := hf.transformNonnegative (2 * Real.pi * ξ)
    have hmath := chapter05_fourierTransform_eq_mathlib_angular f hf.integrable
      (2 * Real.pi * ξ)
    have heq : 𝓕 FC ξ = chapter05FourierTransform f (2 * Real.pi * ξ) := by
      rw [hmath]
      simp only [FC]
      field_simp [Real.pi_ne_zero]
    rw [heq]
    exact hscale
  have hFT_G_nonneg (ξ : ℝ) :
      (𝓕 GC ξ).im = 0 ∧ 0 ≤ (𝓕 GC ξ).re := by
    have hscale := hg.transformNonnegative (2 * Real.pi * ξ)
    have hmath := chapter05_fourierTransform_eq_mathlib_angular g hg.integrable
      (2 * Real.pi * ξ)
    have heq : 𝓕 GC ξ = chapter05FourierTransform g (2 * Real.pi * ξ) := by
      rw [hmath]
      simp only [GC]
      field_simp [Real.pi_ne_zero]
    rw [heq]
    exact hscale
  have hFT_F_cont : Continuous (𝓕 FC) := by
    change Continuous
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) FC)
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hFC
  have hFT_G_cont : Continuous (𝓕 GC) := by
    change Continuous
      (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) GC)
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hGC
  let q : ℝ → ℝ → ℝ → ℂ := fun c v ξ =>
    Complex.exp (-(c⁻¹ : ℂ) * (‖ξ‖ ^ 2 : ℂ) +
      2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫ : ℂ))
  let K : ℝ → ℝ → ℝ → ℂ := fun c v x =>
    ((Real.pi : ℂ) / (c⁻¹ : ℂ)) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
      Complex.exp (-((Real.pi : ℂ) ^ 2) * (‖v - x‖ ^ 2 : ℂ) /
        (c⁻¹ : ℂ))
  have htest : ∀ (c v : ℝ), 0 < c →
      𝓕 (fun ξ : ℝ => Complex.exp
        (-(c⁻¹ : ℂ) * (‖ξ‖ ^ 2 : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫ : ℂ))) =
        (fun x : ℝ =>
          ((Real.pi : ℂ) / (c⁻¹ : ℂ)) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
            Complex.exp (-((Real.pi : ℂ) ^ 2) * (‖v - x‖ ^ 2 : ℂ) /
              (c⁻¹ : ℂ))) := by
    intro c v hc
    funext x
    have h := fourier_gaussian_innerProductSpace'
      (V := ℝ) (b := (c⁻¹ : ℂ)) (by simpa using (inv_pos.mpr hc)) v x
    simpa only using h
  have hqFT (c v : ℝ) (hc : 0 < c) : 𝓕 (q c v) = K c v := by
    simpa [q, K] using htest c v hc
  have hqInt (c v : ℝ) (hc : 0 < c) : Integrable (q c v) volume := by
    simpa [q] using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := ℝ) (b := (c⁻¹ : ℂ))
        (by simpa using (inv_pos.mpr hc)) (2 * Real.pi * Complex.I) v)
  have hreg_g (c v : ℝ) (hc : 0 < c) :
      (∫ x : ℝ, K c v x • GC x ∂volume) =
        ∫ ξ : ℝ, q c v ξ • 𝓕 GC ξ ∂volume := by
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) (e := 𝐞) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner (hqInt c v hc) hGC
    rw [← hqFT c v hc]
    change
      (∫ x : ℝ,
          VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (q c v) x • GC x) =
        ∫ ξ : ℝ,
          q c v ξ • VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) GC ξ
    simpa using hswap
  have hK_gaussian (c v x : ℝ) (hc : 0 < c) :
      K c v x =
        (Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
          Complex.exp (-((Real.pi : ℂ) ^ 2) * (c : ℂ) *
            (‖v - x‖ ^ 2 : ℂ)) := by
    dsimp [K]
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
    have hpow : (Real.pi : ℂ) / (c⁻¹ : ℂ) = (Real.pi * c : ℂ) := by
      field_simp
    rw [hpow]
    congr 2
    field_simp
  have hleft_g_limit (v : ℝ) :
      Tendsto (fun c : ℝ => ∫ x : ℝ, K c v x • GC x ∂volume)
        atTop (𝓝 (GC v)) := by
    have h := Real.tendsto_integral_gaussian_smul' hGC
      (v := v) hGC_cont.continuousAt
    apply h.congr'
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      change
        ((Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
          Complex.exp (-((Real.pi : ℂ) ^ 2) * (c : ℂ) *
            (‖v - x‖ ^ 2 : ℂ))) • GC x = K c v x • GC x
      rw [hK_gaussian c v x hc])
  have hK_norm (c v x : ℝ) (hc : 0 < c) :
      ‖K c v x‖ =
        (Real.pi * c) ^ (1 / 2 : ℝ) *
          Real.exp (-Real.pi ^ 2 * c * ‖v - x‖ ^ 2) := by
    rw [hK_gaussian c v x hc, ← Complex.ofReal_mul, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by
      positivity)]
    rw [Complex.norm_exp]
    norm_num
    left
    have hpi_re : ((Real.pi : ℂ) ^ 2).re = Real.pi ^ 2 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    have hpi_im : ((Real.pi : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    have hdiff_re : (((v : ℂ) - (x : ℂ)) ^ 2).re = (v - x) ^ 2 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    have hdiff_im : (((v : ℂ) - (x : ℂ)) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    rw [hpi_im, hpi_re]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, sq_abs]
  have hK_integral (c v : ℝ) (hc : 0 < c) :
      ∫ x : ℝ, ‖K c v x‖ = 1 := by
    calc
      ∫ x : ℝ, ‖K c v x‖ =
          ∫ x : ℝ, (Real.pi * c) ^ (1 / 2 : ℝ) *
            Real.exp (-Real.pi ^ 2 * c * ‖v - x‖ ^ 2) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => hK_norm c v x hc)
      _ = (Real.pi * c) ^ (1 / 2 : ℝ) *
          ∫ x : ℝ, Real.exp (-Real.pi ^ 2 * c * ‖v - x‖ ^ 2) := by
        rw [integral_const_mul]
      _ = (Real.pi * c) ^ (1 / 2 : ℝ) *
          (Real.pi / (Real.pi ^ 2 * c)) ^ (1 / 2 : ℝ) := by
        have hshift :
            (∫ x : ℝ, Real.exp (-Real.pi ^ 2 * c * ‖v - x‖ ^ 2)) =
              ∫ x : ℝ, Real.exp (-(Real.pi ^ 2 * c) * ‖x‖ ^ 2) := by
          have hcomp :=
            (Measure.measurePreserving_sub_left (volume : Measure ℝ) v).integral_comp
              (MeasurableEquiv.subLeft v).measurableEmbedding
              (fun x : ℝ => Real.exp (-(Real.pi ^ 2 * c) * ‖x‖ ^ 2))
          simpa using hcomp
        rw [hshift]
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ) (by
          positivity)]
        norm_num
      _ = 1 := by
        have hbase : (Real.pi * c) *
            (Real.pi / (Real.pi ^ 2 * c)) = 1 := by
          field_simp
        rw [← Real.mul_rpow (le_of_lt (mul_pos Real.pi_pos hc))
          (div_nonneg (le_of_lt Real.pi_pos)
            (le_of_lt (mul_pos (sq_pos_of_pos Real.pi_pos) hc)))]
        rw [hbase, Real.one_rpow]
  let A : ℝ → ℝ → ℂ := fun c x =>
    ∫ η : ℝ, q c x η • 𝓕 GC η
  have hA_eq (c x : ℝ) (hc : 0 < c) :
      A c x = ∫ y : ℝ, K c x y • GC y := by
    dsimp [A]
    exact (hreg_g c x hc).symm
  have hA_bound (c x : ℝ) (hc : 0 < c) : ‖A c x‖ ≤ Cg := by
    have hgauss0 : Integrable
        (fun y : ℝ => Real.exp (-(Real.pi ^ 2 * c) * ‖y‖ ^ 2)) volume := by
      convert (integrable_rpow_mul_exp_neg_mul_sq
        (b := Real.pi ^ 2 * c) (s := (0 : ℝ)) (by positivity)
        (by norm_num : (-1 : ℝ) < 0)) using 1;
        simp [sq_abs]
    have hgauss_shift : Integrable
        (fun y : ℝ => Real.exp (-(Real.pi ^ 2 * c) * ‖x - y‖ ^ 2)) volume := by
      have hcomp :=
        (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).integrable_comp_of_integrable
          hgauss0
      simpa [Function.comp_def] using hcomp
    have hK_int : Integrable (fun y : ℝ => ‖K c x y‖) volume := by
      have hmul := hgauss_shift.const_mul ((Real.pi * c) ^ (1 / 2 : ℝ))
      apply hmul.congr
      filter_upwards [] with y
      rw [hK_norm c x y hc]
      congr 2
      ring
    have hmajor : Integrable (fun y : ℝ => ‖K c x y‖ * Cg) volume :=
      hK_int.mul_const Cg
    rw [hA_eq c x hc]
    calc
      ‖∫ y : ℝ, K c x y • GC y‖ ≤
          ∫ y : ℝ, ‖K c x y • GC y‖ := norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, ‖K c x y‖ * ‖GC y‖ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => norm_smul _ _)
      _ ≤ ∫ y : ℝ, ‖K c x y‖ * Cg := by
        refine integral_mono_of_nonneg
          (f := fun y : ℝ => ‖K c x y‖ * ‖GC y‖)
          (g := fun y : ℝ => ‖K c x y‖ * Cg)
          (Filter.Eventually.of_forall (fun y =>
            mul_nonneg (norm_nonneg _) (norm_nonneg _))) hmajor ?_
        exact Filter.Eventually.of_forall (fun y =>
          mul_le_mul_of_nonneg_left (by simpa [GC] using hgb y) (norm_nonneg _))
      _ = Cg := by
        rw [integral_mul_const, hK_integral c x hc]
        simp
  have hA_tendsto (x : ℝ) : Tendsto (fun c : ℝ => A c x) atTop (𝓝 (GC x)) := by
    apply (hleft_g_limit x).congr'
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact (hA_eq c x hc).symm
  let C0g : ℝ := ∫ y : ℝ, ‖GC y‖
  have hFT_G_bound (η : ℝ) : ‖𝓕 GC η‖ ≤ C0g := by
    rw [Real.fourier_eq]
    calc
      ‖∫ y : ℝ, 𝐞 (-⟪y, η⟫) • GC y‖ ≤
          ∫ y : ℝ, ‖𝐞 (-⟪y, η⟫) • GC y‖ := norm_integral_le_integral_norm _
      _ = C0g := by
        dsimp [C0g]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by simp)
  have hq_zero (c η : ℝ) :
      q c 0 η = (Real.exp (-(c⁻¹) * ‖η‖ ^ 2) : ℂ) := by
    dsimp [q]
    rw [Complex.ofReal_exp]
    apply congrArg Complex.exp
    have hsq : ((↑|η| : ℂ) ^ 2) = (η : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
    rw [hsq, ← Complex.ofReal_inv]
    simp [Complex.ofReal_neg, Complex.ofReal_mul]
  have hq_phase (c x η : ℝ) :
      q c x η = 𝐞 (x * η) * q c 0 η := by
    rw [hq_zero c η]
    dsimp [q]
    rw [Real.fourierChar_apply, Complex.ofReal_exp]
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    have hsq : ((↑|η| : ℂ) ^ 2) = (η : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
    rw [hsq, ← Complex.ofReal_inv]
    simp [Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  have hA_cont (c : ℝ) (hc : 0 < c) : Continuous (A c) := by
    let Hc : ℝ → ℂ := fun η => q c 0 η • 𝓕 GC η
    have hHc : Integrable Hc volume := by
      dsimp [Hc]
      exact (hqInt c 0 hc).mul_bdd hFT_G_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall hFT_G_bound)
    have hA_inv (x : ℝ) :
        A c x = ∫ η : ℝ, 𝐞 (⟪η, x⟫) • Hc η := by
      dsimp [A, Hc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun η => by
        change q c x η * 𝓕 GC η =
          𝐞 (x * (starRingEnd ℝ) η) • (q c 0 η * 𝓕 GC η)
        rw [hq_phase c x η]
        simp [Circle.smul_def, mul_assoc, mul_comm]
        ring)
    have hcont : Continuous
        (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) Hc) := by
      apply VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar
      · fun_prop
      · exact hHc
    have heq : A c = fun x : ℝ => ∫ η : ℝ, 𝐞 (⟪η, x⟫) • Hc η := by
      funext x
      exact hA_inv x
    rw [heq]
    apply hcont.congr
    intro x
    simp [VectorFourier.fourierIntegral, Hc, smul_eq_mul]
  let C0f : ℝ := ∫ y : ℝ, ‖FC y‖
  have hFT_F_bound (η : ℝ) : ‖𝓕 FC η‖ ≤ C0f := by
    rw [Real.fourier_eq]
    calc
      ‖∫ y : ℝ, 𝐞 (-⟪y, η⟫) • FC y‖ ≤
          ∫ y : ℝ, ‖𝐞 (-⟪y, η⟫) • FC y‖ := norm_integral_le_integral_norm _
      _ = C0f := by
        dsimp [C0f]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by simp)
  have hR_int (c : ℝ) (hc : 0 < c) :
      Integrable (fun x : ℝ => FC x * A c x) volume := by
    exact hFC.mul_bdd (hA_cont c hc).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hA_bound c x hc))
  have hprod_fourier (c : ℝ) (hc : 0 < c) (τ : ℝ) :
      𝓕 (fun x : ℝ => FC x * A c x) τ =
        ∫ η : ℝ, (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η) := by
    let Hc : ℝ → ℂ := fun η => q c 0 η • 𝓕 GC η
    let B : ℝ → ℂ := fun x => 𝐞 (-⟪x, τ⟫) • FC x
    have hHc : Integrable Hc volume := by
      dsimp [Hc]
      exact (hqInt c 0 hc).mul_bdd hFT_G_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall hFT_G_bound)
    have hB : Integrable B volume := by
      dsimp [B]
      exact (VectorFourier.fourierIntegral_convergent_iff
        (V := ℝ) (W := ℝ) (E := ℂ) (μ := volume) (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner τ).2 hFC
    have hA_inv (x : ℝ) :
        A c x = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) Hc x := by
      have hpoint : A c x = ∫ η : ℝ, 𝐞 (⟪η, x⟫) • Hc η := by
        dsimp [A, Hc]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun η => by
          change q c x η * 𝓕 GC η =
            𝐞 (x * (starRingEnd ℝ) η) • (q c 0 η * 𝓕 GC η)
          rw [hq_phase c x η]
          simp [Circle.smul_def, mul_assoc, mul_comm]
          ring)
      rw [hpoint]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun η => by
        simp [Hc, smul_eq_mul])
    have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := -innerₗ ℝ) (e := 𝐞) (μ := volume) (ν := volume)
      Real.continuous_fourierChar (by fun_prop) hHc hB
    rw [Real.fourier_eq]
    dsimp [B]
    calc
      (∫ x : ℝ, 𝐞 (-⟪x, τ⟫) • (FC x * A c x)) =
          ∫ x : ℝ, VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) Hc x • B x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change 𝐞 (-⟪x, τ⟫) • (FC x * A c x) =
            VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) Hc x • B x
          rw [hA_inv x]
          simp [B, Circle.smul_def, mul_assoc, mul_comm, mul_left_comm])
      _ = ∫ η : ℝ, Hc η •
          VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ).flip B η := hswap
      _ = ∫ η : ℝ, (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η) := by
        have hfourier (η : ℝ) :
            VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ).flip B η =
              𝓕 FC (τ - η) := by
          rw [Real.fourier_eq]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by
            change 𝐞 (-((-innerₗ ℝ).flip x) η) • B x =
              𝐞 (-⟪x, τ - η⟫) • FC x
            simp [B, Circle.smul_def, Real.fourierChar_apply]
            rw [← mul_assoc, ← Complex.exp_add]
            congr 1
            ring_nf)
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun η => by
          change Hc η •
              VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ).flip B η =
            (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)
          rw [hfourier η]
          simp [Hc])
  have hT_int (c : ℝ) (hc : 0 < c) (τ : ℝ) :
      Integrable
        (fun η : ℝ => (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)) volume := by
    let Hc : ℝ → ℂ := fun η => q c 0 η • 𝓕 GC η
    have hHc : Integrable Hc volume := by
      dsimp [Hc]
      exact (hqInt c 0 hc).mul_bdd hFT_G_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall hFT_G_bound)
    have hshift : Continuous (fun η : ℝ => 𝓕 FC (τ - η)) := by
      exact hFT_F_cont.comp (continuous_const.sub continuous_id)
    dsimp [Hc]
    exact hHc.mul_bdd hshift.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun η => hFT_F_bound (τ - η)))
  have hq_real (c η : ℝ) :
      (q c 0 η).im = 0 ∧ 0 ≤ (q c 0 η).re := by
    rw [hq_zero c η]
    have him : ((η : ℂ) ^ 2).im = 0 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    have hre : ((η : ℂ) ^ 2).re = η ^ 2 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    norm_num [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_pow, sq_abs, him, hre]
    positivity
  have hT_nonneg (c : ℝ) (hc : 0 < c) (τ η : ℝ) :
      ((q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).im = 0 ∧
        0 ≤ ((q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).re := by
    have hq := hq_real c η
    have hG := hFT_G_nonneg η
    have hF := hFT_F_nonneg (τ - η)
    simp only [smul_eq_mul]
    constructor
    · simp [Complex.mul_im, hq.1, hG.1, hF.1]
    · simp [Complex.mul_re, hq.1, hG.1, hF.1]
      exact mul_nonneg (mul_nonneg hq.2 hG.2) hF.2
  have hR_tendsto (τ : ℝ) :
      Tendsto
          (fun c : ℝ => 𝓕 (fun x : ℝ => FC x * A c x) τ) atTop
        (𝓝 (𝓕 HC τ)) := by
    let R : ℝ → ℝ → ℂ := fun c x =>
      𝐞 (-⟪x, τ⟫) • (FC x * A c x)
    let Rlim : ℝ → ℂ := fun x => 𝐞 (-⟪x, τ⟫) • HC x
    have hphase : Continuous (fun x : ℝ => 𝐞 (-⟪x, τ⟫)) := by
      fun_prop
    have hmeas : ∀ᶠ c : ℝ in atTop, AEStronglyMeasurable (R c) volume := by
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      dsimp [R]
      exact hphase.aestronglyMeasurable.smul
        (hR_int c hc).aestronglyMeasurable
    have hbound : ∀ᶠ c : ℝ in atTop,
        ∀ᵐ x : ℝ ∂volume, ‖R c x‖ ≤ Cg * ‖FC x‖ := by
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      filter_upwards [] with x
      dsimp [R]
      rw [Circle.norm_smul]
      rw [norm_mul]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (hA_bound c x hc) (norm_nonneg (FC x)))
    have hbound_int : Integrable (fun x : ℝ => Cg * ‖FC x‖) volume := by
      simpa only [smul_eq_mul] using hFC.norm.const_mul Cg
    have hlim : ∀ᵐ x : ℝ ∂volume,
        Tendsto (fun c : ℝ => R c x) atTop (𝓝 (Rlim x)) := by
      exact Filter.Eventually.of_forall (fun x => by
        have hmul : Tendsto (fun c : ℝ => FC x * A c x) atTop
            (𝓝 (FC x * GC x)) :=
          tendsto_const_nhds.mul (hA_tendsto x)
        have hsmul := (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => 𝐞 (-⟪x, τ⟫)) atTop
            (𝓝 (𝐞 (-⟪x, τ⟫)))).smul hmul
        simpa [R, Rlim, HC, FC, GC] using hsmul)
    have hD := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (F := R) (f := Rlim) (fun x : ℝ => Cg * ‖FC x‖)
      hmeas hbound hbound_int hlim
    change Tendsto
      (fun c : ℝ => ∫ x : ℝ, 𝐞 (-⟪x, τ⟫) • (FC x * A c x)) atTop
      (𝓝 (∫ x : ℝ, 𝐞 (-⟪x, τ⟫) • HC x))
    simpa only [R, Rlim] using hD
  have hregular_nonneg (c : ℝ) (hc : 0 < c) (τ : ℝ) :
      (𝓕 (fun x : ℝ => FC x * A c x) τ).im = 0 ∧
        0 ≤ (𝓕 (fun x : ℝ => FC x * A c x) τ).re := by
    rw [hprod_fourier c hc τ]
    constructor
    · calc
        (∫ η : ℝ, (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).im =
            ∫ η : ℝ, ((q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).im :=
          (integral_im (hT_int c hc τ)).symm
        _ = 0 := integral_eq_zero_of_ae
          (Filter.Eventually.of_forall (fun η => (hT_nonneg c hc τ η).1))
    · calc
        0 ≤ ∫ η : ℝ, ((q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).re :=
          integral_nonneg_of_ae
            (Filter.Eventually.of_forall (fun η => (hT_nonneg c hc τ η).2))
        _ = (∫ η : ℝ, (q c 0 η • 𝓕 GC η) * 𝓕 FC (τ - η)).re :=
          integral_re (hT_int c hc τ)
  have hHC_nonneg (τ : ℝ) :
      (𝓕 HC τ).im = 0 ∧ 0 ≤ (𝓕 HC τ).re := by
    have him : Tendsto
        (fun c : ℝ => (𝓕 (fun x : ℝ => FC x * A c x) τ).im) atTop
          (𝓝 (𝓕 HC τ).im) := by
      simpa only [Function.comp_def] using
        (Complex.continuous_im.tendsto (𝓕 HC τ)).comp (hR_tendsto τ)
    have hre : Tendsto
        (fun c : ℝ => (𝓕 (fun x : ℝ => FC x * A c x) τ).re) atTop
          (𝓝 (𝓕 HC τ).re) := by
      simpa only [Function.comp_def] using
        (Complex.continuous_re.tendsto (𝓕 HC τ)).comp (hR_tendsto τ)
    have him_zero : Tendsto
        (fun c : ℝ => (𝓕 (fun x : ℝ => FC x * A c x) τ).im) atTop (𝓝 0) := by
      apply Tendsto.congr'
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      exact (hregular_nonneg c hc τ).1.symm
      exact (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    have him_eq : (𝓕 HC τ).im = 0 :=
      (tendsto_nhds_unique him_zero him).symm
    have hre_nonneg : ∀ᶠ c : ℝ in atTop,
        0 ≤ (𝓕 (fun x : ℝ => FC x * A c x) τ).re := by
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
      exact (hregular_nonneg c hc τ).2
    refine ⟨him_eq, ?_⟩
    exact le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) hre
      hre_nonneg
  refine ⟨hfg_cont, hfg_int, ?_⟩
  intro τ
  rw [chapter05_fourierTransform_eq_mathlib_angular
    (fun x : ℝ => f x * g x) hfg_int τ]
  simpa [HC] using hHC_nonneg (τ / (2 * Real.pi))

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
