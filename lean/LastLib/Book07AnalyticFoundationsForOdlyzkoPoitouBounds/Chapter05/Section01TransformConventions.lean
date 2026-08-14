import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Regular

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-! ## 5.1. Transform conventions -/

/-- The angular-frequency convention is Mathlib's Fourier transform evaluated at
`t / (2 * π)`, since pinned Mathlib uses the `2 * π` frequency convention. -/
theorem chapter05_fourierTransform_eq_mathlib_angular
    (F : ℝ → ℝ) (_hF : Integrable F volume) (t : ℝ) :
    chapter05FourierTransform F t =
      𝓕 (fun x : ℝ => (F x : ℂ)) (t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  rw [mul_comm (F x : ℂ)]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Fourier inversion in the normalization used by the Chapter 5 interfaces.

This is the a.e. bridge needed when a later argument works with an arbitrary
complex-valued integrable function rather than a continuous compactly
supported test function. -/
theorem chapter05_fourier_inverse_ae
    {f : ℝ → ℂ} (hF : Integrable f volume)
    (hFourierF : Integrable (𝓕 f) volume) :
    𝓕⁻ (𝓕 f) =ᵐ[volume] f := by
  sorry

theorem chapter05_laplace_reflection
    {F : ℝ → ℝ} (hEven : Function.Even F)
    (_hInt : ∀ s : ℂ,
      Integrable (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x) volume)
    (s : ℂ) :
    chapter05BilateralLaplaceTransform F s =
      chapter05BilateralLaplaceTransform F (1 - s) := by
  unfold chapter05BilateralLaplaceTransform
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume := by
    refine ⟨continuous_neg.measurable, ?_⟩
    simpa only [neg_one_mul, abs_neg, abs_one, inv_neg, inv_one,
      ENNReal.ofReal_one, one_smul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  calc
    (∫ x : ℝ, (F x : ℂ) * chapter05LaplaceKernel s x ∂volume) =
        ∫ x : ℝ, (F (-x) : ℂ) * chapter05LaplaceKernel s (-x) ∂volume := by
      symm
      simpa only using
        (hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding)
          (fun x : ℝ => (F x : ℂ) * chapter05LaplaceKernel s x)
    _ = ∫ x : ℝ, (F x : ℂ) * chapter05LaplaceKernel (1 - s) x ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hEven x]
      simp only [chapter05LaplaceKernel, Complex.ofReal_neg]
      congr 1
      ring_nf

theorem chapter05_laplace_entire_of_continuous_compactSupport
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hCompactSupport : HasCompactSupport F) :
    Differentiable ℂ (chapter05BilateralLaplaceTransform F) := by
  intro z
  let P : ℂ → ℝ → ℂ := fun w x =>
    (F x : ℂ) * Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ))
  let P' : ℂ → ℝ → ℂ →L[ℂ] ℂ := fun w x =>
    ContinuousLinearMap.toSpanSingleton ℂ
      ((F x : ℂ) * (x : ℂ) *
        Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ)))
  let B : ℝ → ℝ := fun x =>
    ‖F x‖ * Real.exp ((‖z‖ + 2) * ‖x‖) * ‖x‖
  have hPcont (w : ℂ) : Continuous (P w) := by
    dsimp [P]
    exact (Complex.continuous_ofReal.comp hContinuous).mul
      (Complex.continuous_exp.comp
        ((continuous_const.sub continuous_const).mul
          (Complex.continuous_ofReal.comp continuous_id)))
  have hPcompact (w : ℂ) : HasCompactSupport (P w) := by
    dsimp [P]
    exact (hCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right
  have hPmeas : ∀ᶠ w in nhds z, AEStronglyMeasurable (P w) volume := by
    exact Filter.Eventually.of_forall fun w => (hPcont w).aestronglyMeasurable
  have hPint (w : ℂ) : Integrable (P w) volume := by
    exact (hPcont w).integrable_of_hasCompactSupport (hPcompact w)
  have hP'cont : Continuous (P' z) := by
    have hcoeff : Continuous (fun x : ℝ =>
        (F x : ℂ) * (x : ℂ) *
          Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ))) := by
      exact ((Complex.continuous_ofReal.comp hContinuous).mul
        (Complex.continuous_ofReal.comp continuous_id)).mul
        (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))
    dsimp [P']
    change Continuous (fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℂ
      ((F x : ℂ) * (x : ℂ) *
        Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ))))
    exact
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).continuous.comp hcoeff
  have hP'meas : AEStronglyMeasurable (P' z) volume :=
    hP'cont.aestronglyMeasurable
  have hBcont : Continuous B := by
    dsimp [B]
    exact (hContinuous.norm.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id.norm))).mul
      continuous_id.norm
  have hBcompact : HasCompactSupport B := by
    dsimp [B]
    exact (hCompactSupport.norm.mul_right).mul_right
  have hBint : Integrable B volume :=
    hBcont.integrable_of_hasCompactSupport hBcompact
  have hbound : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ Metric.closedBall z 1,
      ‖P' w x‖ ≤ B x := by
    filter_upwards [] with x
    intro w hw
    have hw' : ‖w - z‖ ≤ 1 := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hw)
    have hw_norm : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by congr 1; ring
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 + ‖z‖ := add_le_add_left hw' ‖z‖
        _ = ‖z‖ + 1 := by ring
    have hdiff : ‖w - (1 / 2 : ℂ)‖ ≤ ‖z‖ + 2 := by
      have hhalf : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num [Complex.norm_real, Real.norm_eq_abs]
      calc
        ‖w - (1 / 2 : ℂ)‖ ≤ ‖w‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖w‖ + 1 := add_le_add_right hhalf ‖w‖
        _ ≤ (‖z‖ + 1) + 1 := add_le_add_left hw_norm 1
        _ = ‖z‖ + 2 := by ring
    calc
      ‖P' w x‖ = ‖(F x : ℂ) * (x : ℂ) *
          Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ))‖ := by simp [P']
      _ = ‖F x‖ * ‖x‖ *
          ‖Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ))‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖F x‖ * Real.exp (‖(w - (1 / 2 : ℂ)) * (x : ℂ)‖) * ‖x‖ := by
        calc
          ‖F x‖ * ‖x‖ * ‖Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ))‖ =
              ‖F x‖ * ‖Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ))‖ * ‖x‖ := by
                ring
          _ ≤ ‖F x‖ * Real.exp (‖(w - (1 / 2 : ℂ)) * (x : ℂ)‖) * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (Complex.norm_exp_le_exp_norm ((w - (1 / 2 : ℂ)) * (x : ℂ)))
                (norm_nonneg (F x))) (norm_nonneg x)
      _ ≤ ‖F x‖ * Real.exp ((‖z‖ + 2) * ‖x‖) * ‖x‖ := by
        gcongr
        calc
          ‖(w - (1 / 2 : ℂ)) * (x : ℂ)‖ ≤
              ‖w - (1 / 2 : ℂ)‖ * ‖(x : ℂ)‖ := norm_mul_le _ _
          _ ≤ (‖z‖ + 2) * ‖x‖ := by
            simpa only [Complex.norm_real, Real.norm_eq_abs] using
              (mul_le_mul_of_nonneg_right hdiff (abs_nonneg x))
  have hdiff_integrand : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ Metric.closedBall z 1,
      HasFDerivAt (P · x) (P' w x) w := by
    filter_upwards [] with x
    intro w hw
    dsimp [P, P']
    have hlin0 : HasFDerivAt (fun y : ℂ => y)
        (ContinuousLinearMap.id ℂ ℂ) w := hasFDerivAt_id w
    have hlin : HasFDerivAt
        (fun y : ℂ => (y - (1 / 2 : ℂ)) * (x : ℂ))
        ((x : ℂ) • (ContinuousLinearMap.id ℂ ℂ)) w := by
      convert! (hlin0.sub_const (1 / 2 : ℂ)).mul_const (x : ℂ) using 1
    have hexp := hlin.cexp
    have hprod := hexp.const_mul (F x)
    convert! hprod using 1
    ext : 1
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (F := P) (F' := P') (x₀ := z)
    (s := Metric.closedBall z 1) (bound := B)
    (Metric.closedBall_mem_nhds z zero_lt_one) hPmeas (hPint z) hP'meas hbound hBint
      hdiff_integrand
  change DifferentiableAt ℂ
    (fun w : ℂ => ∫ x : ℝ, (F x : ℂ) *
      Complex.exp ((w - (1 / 2 : ℂ)) * (x : ℂ)) ∂volume) z
  exact hderiv.differentiableAt

theorem chapter05_laplace_on_critical_line_eq_fourier_neg
    {F : ℝ → ℝ} {t : ℝ}
    (_hInt : Integrable
      (fun x : ℝ => (F x : ℂ) *
        chapter05LaplaceKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) x) volume) :
    chapter05BilateralLaplaceTransform F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      chapter05FourierTransform F (-t) := by
  unfold chapter05BilateralLaplaceTransform chapter05FourierTransform
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [chapter05LaplaceKernel]
  congr 1
  push_cast
  ring_nf

theorem chapter05_fourier_transform_neg_eq
    {F : ℝ → ℝ} (_hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05FourierTransform F (-t) = chapter05FourierTransform F t := by
  unfold chapter05FourierTransform
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume := by
    refine ⟨continuous_neg.measurable, ?_⟩
    simpa only [neg_one_mul, abs_neg, abs_one, inv_neg, inv_one,
      ENNReal.ofReal_one, one_smul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  calc
    (∫ x : ℝ, (F x : ℂ) * Complex.exp
        (-(Complex.I * (((-t) * x : ℝ) : ℂ))) ∂volume) =
        ∫ x : ℝ, (F (-x) : ℂ) * Complex.exp
          (-(Complex.I * (((-t) * (-x) : ℝ) : ℂ))) ∂volume := by
      symm
      simpa only using
        (hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding)
          (fun x : ℝ => (F x : ℂ) * Complex.exp
            (-(Complex.I * (((-t) * x : ℝ) : ℂ))))
    _ = ∫ x : ℝ, (F x : ℂ) * Complex.exp
        (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hEven x]
      congr 1
      push_cast
      ring_nf

theorem chapter05_laplace_on_critical_line
    {F : ℝ → ℝ} (hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05BilateralLaplaceTransform F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      chapter05FourierTransform F t := by
  have hInt : Integrable
      (fun x : ℝ => (F x : ℂ) *
        chapter05LaplaceKernel ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) x) volume := by
    apply hF.ofReal.mul_bdd
    · exact (Complex.continuous_exp.comp
        ((continuous_const.sub continuous_const).mul
          (Complex.continuous_ofReal.comp continuous_id))).aestronglyMeasurable
    · filter_upwards [] with x
      change ‖Complex.exp (((1 / 2 : ℂ) + (t : ℂ) * Complex.I - (1 / 2 : ℂ)) * (x : ℂ))‖ ≤ 1
      rw [show ((1 / 2 : ℂ) + (t : ℂ) * Complex.I - (1 / 2 : ℂ)) * (x : ℂ) =
          ((t * x : ℝ) : ℂ) * Complex.I by
            push_cast
            ring,
        Complex.norm_exp_ofReal_mul_I]
  calc
    chapter05BilateralLaplaceTransform F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        chapter05FourierTransform F (-t) :=
      chapter05_laplace_on_critical_line_eq_fourier_neg hInt
    _ = chapter05FourierTransform F t := chapter05_fourier_transform_neg_eq hF hEven t

theorem chapter05_fourier_transform_eq_ofReal_real_transform
    {F : ℝ → ℝ} (hF : Integrable F volume) (hEven : Function.Even F) (t : ℝ) :
    chapter05FourierTransform F t =
      (chapter05RealFourierTransform F t : ℂ) := by
  unfold chapter05FourierTransform chapter05RealFourierTransform
  have hFTInt : Integrable
      (fun x : ℝ => (F x : ℂ) *
        Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))) volume := by
    apply hF.ofReal.mul_bdd
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
  have hsinInt : Integrable (fun x : ℝ => F x * Real.sin (t * x)) volume := by
    apply hF.mul_bdd
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · filter_upwards [] with x
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t * x)
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume : Measure ℝ) volume := by
    refine ⟨continuous_neg.measurable, ?_⟩
    simpa only [neg_one_mul, abs_neg, abs_one, inv_neg, inv_one,
      ENNReal.ofReal_one, one_smul] using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hsin_zero : (∫ x : ℝ, F x * Real.sin (t * x) ∂volume) = 0 := by
    have hsymm :
        (∫ x : ℝ, F x * Real.sin (t * x) ∂volume) =
          ∫ x : ℝ, F (-x) * Real.sin (t * (-x)) ∂volume := by
      symm
      simpa only using
        (hneg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding)
          (fun x : ℝ => F x * Real.sin (t * x))
    have hzero :
        (∫ x : ℝ, F x * Real.sin (t * x) ∂volume) =
          -∫ x : ℝ, F x * Real.sin (t * x) ∂volume := by
      calc
        (∫ x : ℝ, F x * Real.sin (t * x) ∂volume) =
            ∫ x : ℝ, F (-x) * Real.sin (t * (-x)) ∂volume := hsymm
        _ = ∫ x : ℝ, -(F x * Real.sin (t * x)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hEven x, mul_neg, Real.sin_neg]
          ring
        _ = -∫ x : ℝ, F x * Real.sin (t * x) ∂volume := by rw [integral_neg]
    linarith
  apply Complex.ext
  · change (∫ x : ℝ, (F x : ℂ) *
      Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume).re =
      ∫ x : ℝ, F x * Real.cos (t * x) ∂volume
    calc
      (∫ x : ℝ, (F x : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume).re =
          ∫ x : ℝ, ((F x : ℂ) *
            Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))).re ∂volume :=
        (integral_re hFTInt).symm
      _ = ∫ x : ℝ, F x * Real.cos (t * x) ∂volume := by
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
  · change (∫ x : ℝ, (F x : ℂ) *
      Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume).im = 0
    calc
      (∫ x : ℝ, (F x : ℂ) *
          Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ))) ∂volume).im =
          ∫ x : ℝ, ((F x : ℂ) *
            Complex.exp (-(Complex.I * ((t * x : ℝ) : ℂ)))).im ∂volume :=
        (integral_im hFTInt).symm
      _ = ∫ x : ℝ, -(F x * Real.sin (t * x)) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        have him : (Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))).im =
            -Real.sin (t * x) := by
          rw [show -(Complex.I * ((t : ℂ) * (x : ℂ))) =
              (((-(t * x) : ℝ) : ℂ) * Complex.I) by
                push_cast
                ring]
          simpa only [Real.sin_neg] using Complex.exp_ofReal_mul_I_im (-(t * x))
        have hre : (Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ))))).re =
            Real.cos (t * x) := by
          rw [show -(Complex.I * ((t : ℂ) * (x : ℂ))) =
              (((-(t * x) : ℝ) : ℂ) * Complex.I) by
                push_cast
                ring]
          simpa only [Real.cos_neg] using Complex.exp_ofReal_mul_I_re (-(t * x))
        simp [Complex.mul_im, hre, him]
      _ = -∫ x : ℝ, F x * Real.sin (t * x) ∂volume := by rw [integral_neg]
      _ = 0 := by rw [hsin_zero]; simp

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
