import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory
open scoped FourierTransform

def chapter07SechHalf (x : ℝ) : ℝ :=
  1 / Real.cosh (x / 2)

def chapter07StripKernel (a : ℝ) (x : ℝ) : ℝ :=
  Real.cosh (a * x) / Real.cosh (x / 2)

def chapter07ComplexSechHalf (z : ℂ) : ℂ :=
  1 / Complex.cosh (z / 2)

def chapter07FourierStrip : Set ℂ :=
  {z | |z.im| < 1 / 2}

theorem chapter07_stripKernel_even (a x : ℝ) :
    chapter07StripKernel a (-x) = chapter07StripKernel a x := by
  rw [chapter07StripKernel, chapter07StripKernel]
  rw [show a * -x = -(a * x) by ring, Real.cosh_neg]
  rw [show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

theorem chapter07_complexSechHalf_periodicity (z : ℂ) :
    chapter07ComplexSechHalf (z + 2 * Real.pi * Complex.I) =
      -chapter07ComplexSechHalf z := by
  simp only [chapter07ComplexSechHalf]
  rw [show (z + 2 * (Real.pi : ℂ) * Complex.I) / 2 =
      z / 2 + (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.cosh_add_pi_mul_I]
  simp

theorem chapter07_sechHalf_transform (t : ℝ) :
    chapter07FourierTransform chapter07SechHalf t =
      (2 * Real.pi / Real.cosh (Real.pi * t) : ℂ) := by
  have hclosed :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_strip_kernel_fourier_closed_form
      (0 : ℝ) t (by norm_num)
  have hkernel : chapter07SechHalf = chapter07StripKernel 0 := by
    funext x
    simp [chapter07SechHalf, chapter07StripKernel]
  have hkernel' : chapter07StripKernel 0 =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05StripKernel 0 := by
    funext x
    simp [chapter07StripKernel,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05StripKernel]
  rw [hkernel]
  rw [hkernel']
  change LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05FourierTransform
    (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05StripKernel 0) t = _
  rw [hclosed]
  norm_num
  have hx : (Real.pi : ℂ) * (t : ℂ) = ((Real.pi * t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) =
      2 * ((Real.pi * t : ℝ) : ℂ) := by
    calc
      (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) =
          2 * ((Real.pi : ℂ) * (t : ℂ)) := by ring
      _ = 2 * ((Real.pi * t : ℝ) : ℂ) := by rw [hx]
  rw [harg, Complex.cosh_two_mul, hx]
  have hcosh : Complex.cosh ((Real.pi * t : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hden : Complex.cosh ((Real.pi * t : ℝ) : ℂ) ^ 2 +
      Complex.sinh ((Real.pi * t : ℝ) : ℂ) ^ 2 + 1 =
      2 * Complex.cosh ((Real.pi * t : ℝ) : ℂ) ^ 2 := by
    rw [Complex.cosh_sq]
    ring
  rw [hden]
  field_simp [hcosh]
  ring

theorem chapter07_sechHalf_integrable :
    Integrable chapter07SechHalf := by
  have hright : IntegrableOn
      (fun x : ℝ => 2 * Real.exp (-(1 / 2 : ℝ) * x)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    change Integrable
      (fun x : ℝ => 2 * Real.exp (-(1 / 2 : ℝ) * x))
      (volume.restrict (Set.Ioi 0))
    simpa [mul_comm, div_eq_mul_inv] using
      (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0).const_mul 2
  have hleft : IntegrableOn
      (fun x : ℝ => 2 * Real.exp ((1 / 2 : ℝ) * x)) (Set.Iic 0) := by
    change Integrable
      (fun x : ℝ => 2 * Real.exp ((1 / 2 : ℝ) * x))
      (volume.restrict (Set.Iic 0))
    simpa using
      (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) 0).const_mul 2
  have hcont : Continuous chapter07SechHalf := by
    unfold chapter07SechHalf
    apply continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hright' : IntegrableOn chapter07SechHalf (Set.Ici 0) := by
    apply Integrable.mono' hright
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      unfold chapter07SechHalf
      have hcosh : Real.cosh (x / 2) ≥ Real.exp (x / 2) / 2 := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (x / 2), Real.exp_pos (-(x / 2))]
      have hden : 0 < Real.cosh (x / 2) := Real.cosh_pos _
      have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.cosh (x / 2))]
      apply (div_le_iff₀ hden).2
      have hprod' : Real.exp (-(1 / 2 : ℝ) * x) * Real.exp (x / 2) = 1 := by
        calc
          Real.exp (-(1 / 2 : ℝ) * x) * Real.exp (x / 2) =
              Real.exp (-(x / 2)) * Real.exp (x / 2) := by
            congr 1
            ring_nf
          _ = Real.exp (x / 2) * Real.exp (-(x / 2)) := by ring
          _ = 1 := hprod
      calc
        1 = 2 * ((Real.exp (-(1 / 2 : ℝ) * x) *
            Real.exp (x / 2)) / 2) := by rw [hprod']; ring
        _ = 2 * (Real.exp (-(1 / 2 : ℝ) * x) *
            (Real.exp (x / 2) / 2)) := by ring
        _ ≤ 2 * (Real.exp (-(1 / 2 : ℝ) * x) * Real.cosh (x / 2)) := by
          gcongr
        _ = 2 * Real.exp (-(1 / 2 : ℝ) * x) * Real.cosh (x / 2) := by ring
  have hleft' : IntegrableOn chapter07SechHalf (Set.Iic 0) := by
    apply Integrable.mono' hleft
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      unfold chapter07SechHalf
      have hcosh : Real.cosh (x / 2) ≥ Real.exp (-(x / 2)) / 2 := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (x / 2), Real.exp_pos (-(x / 2))]
      have hden : 0 < Real.cosh (x / 2) := Real.cosh_pos _
      have hprod : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      have hprod' : Real.exp ((1 / 2 : ℝ) * x) * Real.exp (-(x / 2)) = 1 := by
        calc
          Real.exp ((1 / 2 : ℝ) * x) * Real.exp (-(x / 2)) =
              Real.exp (x / 2) * Real.exp (-(x / 2)) := by
            congr 1
            ring_nf
          _ = 1 := hprod
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.cosh (x / 2))]
      apply (div_le_iff₀ hden).2
      calc
        1 = 2 * ((Real.exp ((1 / 2 : ℝ) * x) *
            Real.exp (-(x / 2))) / 2) := by rw [hprod']; ring
        _ = 2 * (Real.exp ((1 / 2 : ℝ) * x) *
            (Real.exp (-(x / 2)) / 2)) := by ring
        _ ≤ 2 * (Real.exp ((1 / 2 : ℝ) * x) * Real.cosh (x / 2)) := by
          gcongr
        _ = 2 * Real.exp ((1 / 2 : ℝ) * x) * Real.cosh (x / 2) := by ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ici, integrableOn_union]
  exact ⟨hleft', hright'⟩

theorem chapter07_stripKernel_integrable (a : ℝ)
    (ha : |a| < 1 / 2) :
    Integrable (chapter07StripKernel a) := by
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
  have hcont : Continuous (chapter07StripKernel a) := by
    unfold chapter07StripKernel
    apply (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hright' : IntegrableOn (chapter07StripKernel a) (Set.Ici 0) := by
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
      unfold chapter07StripKernel
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le)]
      exact (div_le_iff₀ (Real.cosh_pos _)).2 hbound
  have hleft' : IntegrableOn (chapter07StripKernel a) (Set.Iic 0) := by
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
      unfold chapter07StripKernel
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le)]
      exact (div_le_iff₀ (Real.cosh_pos _)).2 hbound
  rw [← integrableOn_univ, ← Set.Iic_union_Ici, integrableOn_union]
  exact ⟨hleft', hright'⟩

private theorem chapter07_integrable_abs_mul_exp_neg_abs
    {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ => 2 * |x| * Real.exp (-d * |x|)) := by
  have hright : IntegrableOn
      (fun x : ℝ => 2 * x * Real.exp (-d * x)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := d)
      (by norm_num) (by norm_num) hd
    change Integrable (fun x : ℝ => 2 * x * Real.exp (-d * x))
      (volume.restrict (Set.Ioi 0))
    convert h.const_mul 2 using 1
    ext x
    simp only [Real.rpow_one]
    ring
  have hleft : IntegrableOn
      (fun x : ℝ => 2 * (-x) * Real.exp (-d * (-x))) (Set.Iio 0) := by
    change Integrable (fun x : ℝ => 2 * (-x) * Real.exp (-d * (-x)))
      (volume.restrict (Set.Iio 0))
    have hright0 : IntegrableOn
        (fun x : ℝ => 2 * x * Real.exp (-d * x)) (Set.Ioi (-(0 : ℝ))) volume := by
      simpa using hright
    have hcomp : IntegrableOn
        (fun x : ℝ => (2 * (-x) * Real.exp (-d * (-x)))) (Set.Iio 0) volume :=
      MeasureTheory.IntegrableOn.comp_neg_Iio (μ := volume) (c := (0 : ℝ))
        (f := fun x : ℝ => 2 * x * Real.exp (-d * x)) hright0
    exact hcomp
  have hleft' : IntegrableOn
      (fun x : ℝ => 2 * |x| * Real.exp (-d * |x|)) (Set.Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    apply hleft.congr_fun
    · intro x hx
      have hx' : x < 0 := hx
      simp [abs_of_neg hx']
    · exact measurableSet_Iio
  have hright' : IntegrableOn
      (fun x : ℝ => 2 * |x| * Real.exp (-d * |x|)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    apply hright.congr_fun
    · intro x hx
      have hx' : 0 ≤ x := le_of_lt hx
      simp [abs_of_nonneg hx']
    · exact measurableSet_Ioi
  rw [← integrableOn_univ, ← Set.Iic_union_Ici, integrableOn_union]
  exact ⟨hleft', hright'⟩

theorem chapter07_complexSechHalf_transform_holomorphic :
    DifferentiableOn ℂ
      (chapter07ComplexFourierTransform chapter07SechHalf)
      chapter07FourierStrip := by
  intro z hz
  let r : ℝ := |z.im|
  let a : ℝ := (r + 1 / 2) / 2
  let d : ℝ := 1 / 2 - a
  let δ : ℝ := a - r
  have hr : r < 1 / 2 := hz
  have hr_nonneg : 0 ≤ r := abs_nonneg _
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hra : r < a := by
    dsimp [a]
    linarith
  have ha : a < 1 / 2 := by
    dsimp [a]
    linarith
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr hra
  have hcosh_abs (u : ℝ) :
      Real.exp |u| / 2 ≤ Real.cosh u := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu, Real.cosh_eq]
      nlinarith [Real.exp_pos u, Real.exp_pos (-u)]
    · rw [abs_of_nonpos hu, Real.cosh_eq]
      nlinarith [Real.exp_pos u, Real.exp_pos (-u)]
  have hsechcont : Continuous chapter07SechHalf := by
    unfold chapter07SechHalf
    apply continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  let P : ℂ → ℝ → ℂ := fun w x =>
    (chapter07SechHalf x : ℂ) *
      Complex.exp (-Complex.I * w * (x : ℂ))
  let P' : ℂ → ℝ → ℂ →L[ℂ] ℂ := fun w x =>
    ContinuousLinearMap.toSpanSingleton ℂ
      ((chapter07SechHalf x : ℂ) * (-Complex.I) * (x : ℂ) *
        Complex.exp (-Complex.I * w * (x : ℂ)))
  have hPcont (w : ℂ) : Continuous (P w) := by
    dsimp [P]
    fun_prop
  have hPmeas : ∀ᶠ w in nhds z, AEStronglyMeasurable (P w) volume := by
    exact Filter.Eventually.of_forall fun w => (hPcont w).aestronglyMeasurable
  have hstrip : Integrable (chapter07StripKernel a) := by
    apply chapter07_stripKernel_integrable
    rw [abs_of_nonneg ha_nonneg]
    exact ha
  have hPint : Integrable (P z) volume := by
    apply Integrable.mono' (hstrip.const_mul 2)
    · exact (hPcont z).aestronglyMeasurable
    · filter_upwards [] with x
      have harg : z.im * x ≤ a * |x| := by
        calc
          z.im * x ≤ |z.im * x| := le_abs_self _
          _ = |z.im| * |x| := abs_mul _ _
          _ = r * |x| := by rfl
          _ ≤ a * |x| := mul_le_mul_of_nonneg_right (le_of_lt hra) (abs_nonneg _)
      have hexp : Real.exp (z.im * x) ≤ Real.exp (a * |x|) :=
        Real.exp_le_exp.mpr harg
      have habs : |a * x| = a * |x| := by
        rw [abs_mul, abs_of_nonneg ha_nonneg]
      have htwo : Real.exp (a * |x|) ≤ 2 * Real.cosh (a * x) := by
        rw [← habs]
        nlinarith [hcosh_abs (a * x)]
      have hnorm : ‖P z x‖ =
          chapter07SechHalf x * Real.exp (z.im * x) := by
        dsimp [P]
        have hsechpos : 0 < chapter07SechHalf x := by
          unfold chapter07SechHalf
          positivity
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsechpos,
          Complex.norm_exp]
        rw [show (-Complex.I * z * (x : ℂ)).re = z.im * x by
          simp]
      rw [hnorm]
      change (1 / Real.cosh (x / 2)) * Real.exp (z.im * x) ≤
        2 * (Real.cosh (a * x) / Real.cosh (x / 2))
      rw [show (1 / Real.cosh (x / 2)) * Real.exp (z.im * x) =
          Real.exp (z.im * x) / Real.cosh (x / 2) by ring,
        show 2 * (Real.cosh (a * x) / Real.cosh (x / 2)) =
          (2 * Real.cosh (a * x)) / Real.cosh (x / 2) by ring]
      exact (div_le_div_iff_of_pos_right (Real.cosh_pos _)).2
        (hexp.trans htwo)
  have hP'cont : Continuous (P' z) := by
    have hcoeff : Continuous (fun x : ℝ =>
        (chapter07SechHalf x : ℂ) * (-Complex.I) * (x : ℂ) *
          Complex.exp (-Complex.I * z * (x : ℂ))) := by
      fun_prop
    dsimp [P']
    change Continuous (fun x : ℝ => ContinuousLinearMap.toSpanSingleton ℂ
      ((chapter07SechHalf x : ℂ) * (-Complex.I) * (x : ℂ) *
        Complex.exp (-Complex.I * z * (x : ℂ))))
    exact
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).continuous.comp hcoeff
  have hP'meas : AEStronglyMeasurable (P' z) volume :=
    hP'cont.aestronglyMeasurable
  let B : ℝ → ℝ := fun x => 2 * |x| * Real.exp (-d * |x|)
  have hbound : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ Metric.closedBall z δ,
      ‖P' w x‖ ≤ B x := by
    filter_upwards [] with x
    intro w hw
    have hwdiff : |w.im - z.im| ≤ δ := by
      calc
        |w.im - z.im| = |(w - z).im| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = dist w z := (dist_eq_norm w z).symm
        _ ≤ δ := Metric.mem_closedBall.mp hw
    have him : |w.im| ≤ a := by
      calc
        |w.im| = |z.im + (w.im - z.im)| := by congr 1; ring
        _ ≤ |z.im| + |w.im - z.im| := by
          simpa only [Real.norm_eq_abs] using
            (norm_add_le z.im (w.im - z.im))
        _ ≤ r + δ := add_le_add (le_rfl) hwdiff
        _ = a := by dsimp [δ]; ring
    have harg : w.im * x ≤ a * |x| := by
      calc
        w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ a * |x| := mul_le_mul_of_nonneg_right him (abs_nonneg _)
    have hexp : Real.exp (w.im * x) ≤ Real.exp (a * |x|) :=
      Real.exp_le_exp.mpr harg
    have habs : |x / 2| = |x| / 2 := by
      rw [abs_div]
      norm_num
    have hlower : Real.exp (|x| / 2) / 2 ≤ Real.cosh (x / 2) := by
      convert hcosh_abs (x / 2) using 1
      rw [habs]
    have hsech : chapter07SechHalf x ≤ 2 * Real.exp (-|x| / 2) := by
      unfold chapter07SechHalf
      apply (div_le_iff₀ (Real.cosh_pos _)).2
      calc
        1 = Real.exp (-|x| / 2) * Real.exp (|x| / 2) := by
          rw [← Real.exp_add]
          rw [show -|x| / 2 + |x| / 2 = 0 by ring]
          simp
        _ = 2 * Real.exp (-|x| / 2) * (Real.exp (|x| / 2) / 2) := by ring
        _ ≤ 2 * Real.exp (-|x| / 2) * Real.cosh (x / 2) := by
          gcongr
    have hsechpos : 0 < chapter07SechHalf x := by
      unfold chapter07SechHalf
      positivity
    have hprod : chapter07SechHalf x * |x| * Real.exp (w.im * x) ≤
        2 * |x| * Real.exp (-d * |x|) := by
      calc
        chapter07SechHalf x * |x| * Real.exp (w.im * x) ≤
            chapter07SechHalf x * |x| * Real.exp (a * |x|) := by
          gcongr
        _ ≤ (2 * Real.exp (-|x| / 2)) * |x| * Real.exp (a * |x|) := by
          gcongr
        _ = 2 * |x| * Real.exp (-d * |x|) := by
          calc
            (2 * Real.exp (-|x| / 2)) * |x| * Real.exp (a * |x|) =
                2 * |x| * (Real.exp (-|x| / 2) * Real.exp (a * |x|)) := by ring
            _ = 2 * |x| * Real.exp (-d * |x|) := by
              rw [← Real.exp_add]
              congr 3
              dsimp [d]
              ring
    have hnorm : ‖P' w x‖ =
        chapter07SechHalf x * |x| * Real.exp (w.im * x) := by
      dsimp [P']
      have hsechpos : 0 < chapter07SechHalf x := by
        unfold chapter07SechHalf
        positivity
      simp only [ContinuousLinearMap.norm_toSpanSingleton, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos
          hsechpos, norm_neg, Complex.norm_I, Complex.norm_exp]
      rw [show (-Complex.I * w * (x : ℂ)).re = w.im * x by
        simp]
      ring
    rw [hnorm]
    exact hprod
  have hdiff_integrand : ∀ᵐ x : ℝ ∂volume, ∀ w ∈ Metric.closedBall z δ,
      HasFDerivAt (P · x) (P' w x) w := by
    filter_upwards [] with x
    intro w hw
    dsimp [P, P']
    have hlin0 : HasFDerivAt (fun y : ℂ => y)
        (ContinuousLinearMap.id ℂ ℂ) w := hasFDerivAt_id w
    have hlin : HasFDerivAt
        (fun y : ℂ => -Complex.I * y * (x : ℂ))
        ((-Complex.I * (x : ℂ)) • (ContinuousLinearMap.id ℂ ℂ)) w := by
      convert! (hlin0.const_mul (-Complex.I)).mul_const (x : ℂ) using 1
      ext : 1
      simp [smul_eq_mul]
      ring
    have hexp := hlin.cexp
    have hprod := hexp.const_mul (chapter07SechHalf x)
    convert! hprod using 1
    ext : 1
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (F := P) (F' := P') (x₀ := z)
    (s := Metric.closedBall z δ) (bound := B)
    (Metric.closedBall_mem_nhds z hδ) hPmeas hPint hP'meas hbound
      (chapter07_integrable_abs_mul_exp_neg_abs hd) hdiff_integrand
  have hAt : DifferentiableAt ℂ
      (fun w : ℂ => ∫ x : ℝ, P w x) z := hderiv.differentiableAt
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => ∫ x : ℝ, (chapter07SechHalf x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - Complex.I * w - (1 / 2 : ℂ)) * (x : ℂ)))
    chapter07FourierStrip z
  have hfun : (fun w : ℂ => ∫ x : ℝ, P w x) =
      (fun w : ℂ => ∫ x : ℝ, (chapter07SechHalf x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - Complex.I * w - (1 / 2 : ℂ)) * (x : ℂ))) := by
    funext w
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [P]
    congr 1
    norm_num
  rw [← hfun]
  exact hAt.differentiableWithinAt

theorem chapter07_complexSechHalf_closed_form_holomorphic :
    DifferentiableOn ℂ
      (fun z : ℂ => (2 * Real.pi : ℂ) / Complex.cosh (Real.pi * z))
      chapter07FourierStrip := by
  apply DifferentiableOn.div
  · fun_prop
  · intro z hz
    exact (Complex.differentiableAt_cosh.comp z (by fun_prop)).differentiableWithinAt
  · intro z hz
    have hz' : |z.im| < 1 / 2 := hz
    have harg :
        (Real.pi : ℂ) * z =
          ((Real.pi * z.re : ℝ) : ℂ) + ((Real.pi * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    intro hzero
    rw [harg, Complex.cosh_add, ← Complex.ofReal_cosh,
      Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      Complex.sinh_mul_I, ← Complex.ofReal_sin] at hzero
    have hzero' :
        ((Real.cosh (Real.pi * z.re) : ℂ) *
            (Real.cos (Real.pi * z.im) : ℂ) +
          (Real.sinh (Real.pi * z.re) : ℂ) *
            ((Real.sin (Real.pi * z.im) : ℂ) * Complex.I)) = 0 := by
      simpa only [← Complex.ofReal_mul, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_sin] using hzero
    have hreal := congrArg Complex.re hzero'
    have hzlo : -(1 / 2 : ℝ) < z.im := (abs_lt.mp hz').1
    have hzhi : z.im < 1 / 2 := (abs_lt.mp hz').2
    have hcos : 0 < Real.cos (Real.pi * z.im) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos, hzlo, hzhi]
    have hpos : 0 < Real.cosh (Real.pi * z.re) * Real.cos (Real.pi * z.im) :=
      mul_pos (Real.cosh_pos _) hcos
    have hreal' : Real.cosh (Real.pi * z.re) * Real.cos (Real.pi * z.im) = 0 := by
      simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        sub_zero, zero_sub, add_zero, Complex.zero_re] using hreal
    exact (ne_of_gt hpos) hreal'

theorem chapter07_complexSechHalf_transform (z : ℂ)
    (hz : z ∈ chapter07FourierStrip) :
    chapter07ComplexFourierTransform chapter07SechHalf z =
      (2 * Real.pi : ℂ) / Complex.cosh (Real.pi * z) := by
  have hopen : IsOpen chapter07FourierStrip := by
    unfold chapter07FourierStrip
    apply isOpen_lt
    · fun_prop
    · fun_prop
  have hconv : Convex ℝ chapter07FourierStrip := by
    intro u hu v hv a b ha hb hab
    change |(a • u + b • v).im| < 1 / 2
    have hu' : |u.im| < 1 / 2 := hu
    have hv' : |v.im| < 1 / 2 := hv
    have htri : |a * u.im + b * v.im| ≤
        |a * u.im| + |b * v.im| := by
      simpa only [Real.norm_eq_abs] using
        (norm_add_le (a * u.im) (b * v.im))
    have hstrict : a * |u.im| + b * |v.im| < 1 / 2 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by nlinarith
        simpa [ha0, hb1] using hv'
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hu_mul : a * |u.im| < a * (1 / 2) :=
          mul_lt_mul_of_pos_left hu' ha_pos
        have hv_mul : b * |v.im| ≤ b * (1 / 2) :=
          mul_le_mul_of_nonneg_left hv'.le hb
        calc
          a * |u.im| + b * |v.im| < a * (1 / 2) + b * (1 / 2) := by
            nlinarith
          _ = 1 / 2 := by nlinarith
    rw [show (a • u + b • v).im = a * u.im + b * v.im by simp]
    exact htri.trans_lt (by simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      using hstrict)
  have hf_an : AnalyticOnNhd ℂ
      (chapter07ComplexFourierTransform chapter07SechHalf)
      chapter07FourierStrip :=
    chapter07_complexSechHalf_transform_holomorphic.analyticOnNhd hopen
  have hg_an : AnalyticOnNhd ℂ
      (fun w : ℂ => (2 * Real.pi : ℂ) / Complex.cosh (Real.pi * w))
      chapter07FourierStrip :=
    chapter07_complexSechHalf_closed_form_holomorphic.analyticOnNhd hopen
  have hzero : (0 : ℂ) ∈ chapter07FourierStrip := by
    change |(0 : ℂ).im| < 1 / 2
    norm_num
  have hacc : (0 : ℂ) ∈ closure
      ({w : ℂ | chapter07ComplexFourierTransform chapter07SechHalf w =
          (2 * Real.pi : ℂ) / Complex.cosh (Real.pi * w)} \ {(0 : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · constructor
      · calc
          chapter07ComplexFourierTransform chapter07SechHalf ((ε / 2 : ℝ) : ℂ) =
              chapter07FourierTransform chapter07SechHalf (ε / 2) :=
            chapter07ComplexFourierTransform_ofReal chapter07SechHalf (ε / 2 : ℝ)
          _ = (2 * Real.pi / Real.cosh (Real.pi * (ε / 2)) : ℂ) :=
            chapter07_sechHalf_transform (ε / 2 : ℝ)
          _ = (2 * Real.pi : ℂ) /
              Complex.cosh (Real.pi * ((ε / 2 : ℝ) : ℂ)) := by
            have harg : (Real.pi : ℂ) * ((ε / 2 : ℝ) : ℂ) =
                ((Real.pi * (ε / 2) : ℝ) : ℂ) := by
              norm_num
            rw [harg, ← Complex.ofReal_cosh]
      · intro hzero'
        have hreal := congrArg Complex.re hzero'
        have : (ε / 2 : ℝ) = 0 := by
          simpa using hreal
        linarith
    · calc
        dist (0 : ℂ) ((ε / 2 : ℝ) : ℂ) =
            ‖((ε / 2 : ℝ) : ℂ)‖ := by
              rw [dist_comm, dist_zero_right]
        _ = |ε / 2| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
        _ < ε := by
          rw [abs_div, abs_of_pos (by linarith : 0 < ε)]
          norm_num
          linarith
  have hEqOn := hf_an.eqOn_of_preconnected_of_mem_closure hg_an
    hconv.isPreconnected hzero hacc
  exact hEqOn hz

theorem chapter07_stripKernel_eq_exp_average_mul_sech (a x : ℝ) :
    chapter07StripKernel a x =
      ((Real.exp (a * x) + Real.exp (-a * x)) / 2) * chapter07SechHalf x := by
  simp only [chapter07StripKernel, chapter07SechHalf]
  have hcosh : Real.cosh (a * x) =
      (Real.exp (a * x) + Real.exp (-(a * x))) / 2 := by
    simp [Real.cosh, Complex.cosh, Complex.exp_re]
  rw [hcosh]
  ring_nf

theorem chapter07_stripKernel_endpoint (a x : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter07StripKernel a x = 1 := by
  rcases ha with rfl | rfl
  · have hden : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    rw [chapter07StripKernel, show (1 / 2 : ℝ) * x = x / 2 by ring]
    exact div_self hden
  · have hden : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    rw [chapter07StripKernel, show -(1 / 2 : ℝ) * x = -(x / 2) by ring,
      Real.cosh_neg]
    exact div_self hden

theorem chapter07_stripKernel_half (x : ℝ) :
    chapter07StripKernel (1 / 2 : ℝ) x = 1 := by
  exact chapter07_stripKernel_endpoint (1 / 2 : ℝ) x (Or.inl rfl)

theorem chapter07_stripKernel_neg_half (x : ℝ) :
    chapter07StripKernel (-(1 / 2 : ℝ)) x = 1 := by
  exact chapter07_stripKernel_endpoint (-(1 / 2 : ℝ)) x (Or.inr rfl)

theorem chapter07_stripKernel_fourier_shift_formula (a t : ℝ)
    (ha : |a| < 1 / 2) :
    chapter07FourierTransform (chapter07StripKernel a) t =
      (Real.pi : ℂ) *
        (1 / Complex.cosh (Real.pi * ((t : ℂ) + Complex.I * (a : ℂ))) +
          1 / Complex.cosh (Real.pi * ((t : ℂ) - Complex.I * (a : ℂ)))) := by
  have hsechcont : Continuous chapter07SechHalf := by
    unfold chapter07SechHalf
    apply continuous_const.div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hweighted : ∀ b : ℝ, |b| < 1 / 2 →
      Integrable (fun x : ℝ => Real.exp (b * x) * chapter07SechHalf x) := by
    intro b hb
    have hstrip := chapter07_stripKernel_integrable b hb
    have hcont : Continuous (fun x : ℝ =>
        Real.exp (b * x) * chapter07SechHalf x) := by
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hsechcont
    apply Integrable.mono' (hstrip.const_mul 2)
    · exact hcont.aestronglyMeasurable
    · filter_upwards [] with x
      have hsech : 0 ≤ chapter07SechHalf x := by
        unfold chapter07SechHalf
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.exp_pos _).le hsech)]
      calc
        Real.exp (b * x) * chapter07SechHalf x ≤
            (Real.exp (b * x) + Real.exp (-b * x)) *
              chapter07SechHalf x := by
          gcongr
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        _ = 2 * chapter07StripKernel b x := by
          rw [chapter07_stripKernel_eq_exp_average_mul_sech]
          ring
  have hphase (b : ℝ) (hb : |b| < 1 / 2) :
      Integrable (fun x : ℝ =>
        (Real.exp (b * x) * chapter07SechHalf x : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
    apply Integrable.mono' (hweighted b hb)
    · have hrealcont : Continuous (fun x : ℝ =>
          Real.exp (b * x) * chapter07SechHalf x) := by
        exact (Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul hsechcont
      have hphasecont : Continuous (fun x : ℝ =>
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
        exact Complex.continuous_exp.comp
          ((continuous_const.mul continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id))
      have hcont : Continuous (fun x : ℝ =>
          (Real.exp (b * x) : ℂ) * (chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
        exact ((Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          (Complex.continuous_ofReal.comp hsechcont)).mul hphasecont
      exact hcont.aestronglyMeasurable
    · filter_upwards [] with x
      have hsech : 0 ≤ chapter07SechHalf x := by
        unfold chapter07SechHalf
        positivity
      rw [show -Complex.I * (t : ℂ) * (x : ℂ) =
          (((-(t * x) : ℝ) : ℂ) * Complex.I) by
            push_cast
            ring,
        norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg hsech,
        Complex.norm_exp_ofReal_mul_I]
      simp
  have hshift (b : ℝ) (hb : |b| < 1 / 2) :
      chapter07FourierTransform
          (fun x : ℝ => Real.exp (b * x) * chapter07SechHalf x) t =
        chapter07ComplexFourierTransform chapter07SechHalf
          ((t : ℂ) + Complex.I * (b : ℂ)) := by
    rw [chapter07FourierTransform_eq_integral]
    unfold chapter07ComplexFourierTransform
    unfold LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Complex.ofReal_mul, Complex.ofReal_exp]
    calc
      Complex.exp ((b : ℂ) * (x : ℂ)) * (chapter07SechHalf x : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
          (chapter07SechHalf x : ℂ) *
            (Complex.exp ((b : ℂ) * (x : ℂ)) *
              Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by ring
      _ = (chapter07SechHalf x : ℂ) *
          Complex.exp ((b : ℂ) * (x : ℂ) +
            (-Complex.I * (t : ℂ) * (x : ℂ))) := by
        rw [← Complex.exp_add]
      _ = _ := by
        congr 2
        ring_nf
        simp
  have hplus := hphase a ha
  have hminus : |(-a : ℝ)| < 1 / 2 := by simpa using ha
  have hminus' := hphase (-a) hminus
  calc
    chapter07FourierTransform (chapter07StripKernel a) t =
        ∫ x : ℝ, (chapter07StripKernel a x : ℂ) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
      rw [chapter07FourierTransform_eq_integral]
    _ = ∫ x : ℝ,
        (((Real.exp (a * x) + Real.exp (-a * x)) / 2) *
          chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [chapter07_stripKernel_eq_exp_average_mul_sech]
      simp only [Complex.ofReal_mul, Complex.ofReal_add,
        Complex.ofReal_div]
      norm_num
    _ = ∫ x : ℝ, (1 / 2 : ℂ) *
        (((Real.exp (a * x) * chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) +
          ((Real.exp (-a * x) * chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      push_cast
      norm_num; ring
    _ = (1 / 2 : ℂ) *
        ((∫ x : ℝ, (Real.exp (a * x) : ℂ) * (chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) +
          ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * (chapter07SechHalf x : ℂ) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) := by
      rw [integral_const_mul, integral_add hplus hminus']
    _ = (1 / 2 : ℂ) *
        (chapter07FourierTransform
            (fun x : ℝ => Real.exp (a * x) * chapter07SechHalf x) t +
          chapter07FourierTransform
            (fun x : ℝ => Real.exp (-a * x) * chapter07SechHalf x) t) := by
      rw [chapter07FourierTransform_eq_integral,
        chapter07FourierTransform_eq_integral]
      simp only [Complex.ofReal_mul]
    _ = (1 / 2 : ℂ) *
        (chapter07ComplexFourierTransform chapter07SechHalf
            ((t : ℂ) + Complex.I * (a : ℂ)) +
          chapter07ComplexFourierTransform chapter07SechHalf
            ((t : ℂ) + Complex.I * ((-a : ℝ) : ℂ))) := by
      rw [hshift a ha, hshift (-a) hminus]
    _ = (Real.pi : ℂ) *
        (1 / Complex.cosh (Real.pi * ((t : ℂ) + Complex.I * (a : ℂ))) +
          1 / Complex.cosh (Real.pi * ((t : ℂ) - Complex.I * (a : ℂ)))) := by
      rw [chapter07_complexSechHalf_transform
        ((t : ℂ) + Complex.I * (a : ℂ)) (by
          change |((t : ℂ) + Complex.I * (a : ℂ)).im| < 1 / 2
          simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_im,
            Complex.I_re, Complex.I_im, zero_mul,
            one_mul]
          simpa using ha),
        chapter07_complexSechHalf_transform
        ((t : ℂ) + Complex.I * ((-a : ℝ) : ℂ)) (by
          change |((t : ℂ) + Complex.I * ((-a : ℝ) : ℂ)).im| < 1 / 2
          simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_im,
            Complex.I_re, Complex.I_im, zero_mul,
            one_mul]
          simpa [abs_neg] using ha)]
      have harg : (t : ℂ) + Complex.I * ((-a : ℝ) : ℂ) =
          (t : ℂ) - Complex.I * (a : ℂ) := by
        push_cast
        ring
      rw [harg]
      ring

theorem chapter07_stripKernel_fourier_closed_form (a t : ℝ)
    (ha : |a| < 1 / 2) :
    chapter07FourierTransform (chapter07StripKernel a) t =
      (4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a)) : ℂ) := by
  rw [chapter07_stripKernel_fourier_shift_formula a t ha]
  have ha' : -(1 / 2 : ℝ) < a ∧ a < 1 / 2 := abs_lt.mp ha
  have hcos : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hplus :
      Complex.cosh (Real.pi * ((t : ℂ) + Complex.I * (a : ℂ))) =
        (((Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) : ℝ) : ℂ) +
          ((Real.sinh (Real.pi * t) * Real.sin (Real.pi * a) : ℝ) : ℂ) *
            Complex.I) := by
    have harg :
        (Real.pi : ℂ) * ((t : ℂ) + Complex.I * (a : ℂ)) =
          ((Real.pi * t : ℝ) : ℂ) + ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
      norm_num
      ring
    rw [harg, Complex.cosh_add, ← Complex.ofReal_cosh,
      Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    norm_num
    ring
  have hminus :
      Complex.cosh (Real.pi * ((t : ℂ) - Complex.I * (a : ℂ))) =
        (((Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) : ℝ) : ℂ) -
          ((Real.sinh (Real.pi * t) * Real.sin (Real.pi * a) : ℝ) : ℂ) *
            Complex.I) := by
    have harg :
        (Real.pi : ℂ) * ((t : ℂ) - Complex.I * (a : ℂ)) =
          ((Real.pi * t : ℝ) : ℂ) - ((Real.pi * a : ℝ) : ℂ) * Complex.I := by
      norm_num
      ring
    rw [harg, Complex.cosh_sub, ← Complex.ofReal_cosh,
      Complex.cosh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    norm_num
    ring
  have hplus_ne :
      Complex.cosh (Real.pi * ((t : ℂ) + Complex.I * (a : ℂ))) ≠ 0 := by
    rw [hplus]
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) :=
      mul_pos (Real.cosh_pos _) hcos
    have hreal' : Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) = 0 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.zero_re] using hreal
    exact (ne_of_gt hpos) hreal'
  have hminus_ne :
      Complex.cosh (Real.pi * ((t : ℂ) - Complex.I * (a : ℂ))) ≠ 0 := by
    rw [hminus]
    intro hzero
    have hreal := congrArg Complex.re hzero
    have hpos : 0 < Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) :=
      mul_pos (Real.cosh_pos _) hcos
    have hreal' : Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) = 0 := by
      simpa only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.zero_re] using hreal
    exact (ne_of_gt hpos) hreal'
  have hden : 0 <
      Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
      Real.cosh_two_mul, show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
      Real.cos_two_mul]
    nlinarith [Real.cosh_sq (Real.pi * t),
      Real.sin_sq_add_cos_sq (Real.pi * a),
      sq_nonneg (Real.sinh (Real.pi * t))]
  have hden_cast :
      Complex.cosh ((Real.pi : ℂ) * (t : ℂ) * 2) +
          Complex.cos ((Real.pi : ℂ) * (a : ℂ) * 2) =
        (((Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) : ℝ) : ℂ)) := by
    rw [show (Real.pi : ℂ) * (t : ℂ) * 2 =
        ((2 * Real.pi * t : ℝ) : ℂ) by norm_num; ring,
      show (Real.pi : ℂ) * (a : ℂ) * 2 =
        ((2 * Real.pi * a : ℝ) : ℂ) by norm_num; ring,
      ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_add]
  have hden_complex :
      Complex.cosh ((Real.pi : ℂ) * (t : ℂ) * 2) +
          Complex.cos ((Real.pi : ℂ) * (a : ℂ) * 2) ≠ 0 := by
    rw [hden_cast]
    exact Complex.ofReal_ne_zero.mpr hden.ne'
  field_simp [hplus_ne, hminus_ne, hden_complex]
  rw [hplus, hminus]
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * a)
  have hhyper := Real.cosh_sq (Real.pi * t)
  have hden_real :
      Real.cosh (Real.pi * t * 2) + Real.cos (Real.pi * a * 2) =
        2 * (Real.sinh (Real.pi * t) ^ 2 + Real.cos (Real.pi * a) ^ 2) := by
    rw [show Real.pi * t * 2 = 2 * (Real.pi * t) by ring,
      Real.cosh_two_mul, show Real.pi * a * 2 = 2 * (Real.pi * a) by ring,
      Real.cos_two_mul]
    nlinarith [htrig, hhyper]
  have hden_split :
      (((Real.cosh (Real.pi * t * 2) : ℝ) : ℂ) +
        ((Real.cos (Real.pi * a * 2) : ℝ) : ℂ)) =
      ((Real.cosh (Real.pi * t * 2) + Real.cos (Real.pi * a * 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
  rw [hden_split, hden_real]
  have hsquare : Real.sin (Real.pi * a) ^ 2 = 1 - Real.cos (Real.pi * a) ^ 2 := by
    nlinarith [htrig]
  have hcubic : Real.cosh (Real.pi * t) ^ 3 =
      Real.cosh (Real.pi * t) * (Real.sinh (Real.pi * t) ^ 2 + 1) := by
    calc
      Real.cosh (Real.pi * t) ^ 3 =
          Real.cosh (Real.pi * t) * Real.cosh (Real.pi * t) ^ 2 := by ring
      _ = Real.cosh (Real.pi * t) * (Real.sinh (Real.pi * t) ^ 2 + 1) := by
        rw [hhyper]
  have hreal :
      Real.cosh (Real.pi * t) * Real.cos (Real.pi * a) *
          (Real.cos (Real.pi * a) ^ 2 * 2 + Real.sinh (Real.pi * t) ^ 2 * 2) * 2 =
        (Real.cosh (Real.pi * t) * Real.cos (Real.pi * a)) ^ 2 *
            Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) * 4 +
          (Real.sinh (Real.pi * t) * Real.sin (Real.pi * a)) ^ 2 *
            Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) * 4 := by
    calc
      _ = Real.cosh (Real.pi * t) ^ 3 * Real.cos (Real.pi * a) ^ 3 * 4 +
          Real.sinh (Real.pi * t) ^ 2 * Real.sin (Real.pi * a) ^ 2 *
            Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) * 4 := by
              rw [hsquare, hcubic]
              ring
      _ = _ := by ring
  ring_nf
  rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
  norm_num
  have hct : (Real.pi : ℂ) * (t : ℂ) = ((Real.pi * t : ℝ) : ℂ) := by
    norm_num
  have hca : (Real.pi : ℂ) * (a : ℂ) = ((Real.pi * a : ℝ) : ℂ) := by
    norm_num
  rw [hct, hca, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
  have hcomplex := congrArg (fun z : ℝ => (z : ℂ)) hreal
  norm_num at hcomplex ⊢
  exact hcomplex

theorem chapter07_stripKernel_denominator_identity (a t : ℝ) :
    Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) =
      2 * (Real.sinh (Real.pi * t) ^ 2 + Real.cos (Real.pi * a) ^ 2) := by
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    Real.cosh_two_mul, show 2 * Real.pi * a = 2 * (Real.pi * a) by ring,
    Real.cos_two_mul]
  nlinarith [Real.cosh_sq (Real.pi * t),
    Real.sin_sq_add_cos_sq (Real.pi * a)]

theorem chapter07_stripKernel_denominator_pos (a t : ℝ)
    (ha : |a| < 1 / 2) :
    0 < Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a) := by
  rw [chapter07_stripKernel_denominator_identity]
  have ha' : -(1 / 2 : ℝ) < a ∧ a < 1 / 2 := (abs_lt.mp ha)
  have hcos : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  nlinarith [sq_nonneg (Real.sinh (Real.pi * t)), sq_pos_of_pos hcos]

theorem chapter07_stripKernel_numerator_nonnegative (a t : ℝ)
    (ha : |a| < 1 / 2) :
    0 ≤ 4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) := by
  have ha' : -(1 / 2 : ℝ) < a ∧ a < 1 / 2 := (abs_lt.mp ha)
  have hcos : 0 < Real.cos (Real.pi * a) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  positivity

theorem chapter07_stripKernel_fourier_nonnegative (a : ℝ)
    (ha : |a| < 1 / 2) :
    chapter07FourierNonnegative (chapter07StripKernel a) := by
  refine ⟨chapter07_stripKernel_integrable a ha, ?_⟩
  intro t
  rw [chapter07_stripKernel_fourier_closed_form a t ha]
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
  · change 0 ≤
      4 * Real.pi * Real.cos (Real.pi * a) * Real.cosh (Real.pi * t) /
        (Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * a))
    exact div_nonneg (chapter07_stripKernel_numerator_nonnegative a t ha)
      (chapter07_stripKernel_denominator_pos a t ha).le
  · rfl

theorem chapter07_stripKernel_positiveType (a : ℝ)
    (ha : |a| < 1 / 2) :
    chapter07PositiveType (chapter07StripKernel a) := by
  have hcont : Continuous (chapter07StripKernel a) := by
    unfold chapter07StripKernel
    apply (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
    intro x
    exact (Real.cosh_pos _).ne'
  have hfourier := chapter07_stripKernel_fourier_nonnegative a ha
  refine ⟨hcont, hfourier.1, ?_⟩
  intro t
  exact ⟨(hfourier.2 t).2, (hfourier.2 t).1⟩

def chapter07ConstantFourierMeasure : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi) • Measure.dirac 0

theorem chapter07_constant_one_fourier_representation :
    chapter07TemperedFourierRepresentation (fun _ : ℝ => 1)
      chapter07ConstantFourierMeasure := by
  intro φ
  have hφ : Integrable (φ : ℝ → ℂ) := φ.integrable
  have hφhat : Integrable (𝓕 (φ : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 φ).integrable
  have hzero : (∫ t : ℝ, 𝓕 (φ : ℝ → ℂ) t) = φ 0 := by
    have hinv := congrFun
      (φ.continuous.fourierInv_fourier_eq hφ hφhat) 0
    simpa [Real.fourierInv_eq] using hinv
  have hinner (x : ℝ) :
      (∫ t : ℝ, φ t * Complex.exp
        (-Complex.I * (t : ℂ) * (x : ℂ))) =
        𝓕 (φ : ℝ → ℂ) (x / (2 * Real.pi)) := by
    rw [Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    calc
      φ t * Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) =
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) * φ t := by
        rw [mul_comm]
      _ = Complex.exp (↑(2 * Real.pi * -inner ℝ t (x / (2 * Real.pi))) * Complex.I) *
          φ t := by
        congr 1
        rw [Real.inner_apply]
        norm_num
        congr 1
        field_simp [Real.pi_ne_zero]
  unfold chapter07FourierDistributionPairing
  change (∫ x : ℝ, (1 : ℂ) * (∫ t : ℝ, φ t * Complex.exp
      (-Complex.I * (t : ℂ) * (x : ℂ)))) =
    ∫ t : ℝ, φ t ∂chapter07ConstantFourierMeasure
  simp only [one_mul]
  calc
    (∫ x : ℝ, (∫ t : ℝ, φ t * Complex.exp
        (-Complex.I * (t : ℂ) * (x : ℂ)))) =
        ∫ x : ℝ, 𝓕 (φ : ℝ → ℂ) (x / (2 * Real.pi)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hinner x
    _ = |2 * Real.pi| • (∫ t : ℝ, 𝓕 (φ : ℝ → ℂ) t) := by
      rw [Measure.integral_comp_div]
    _ = (2 * Real.pi) • φ 0 := by
      rw [abs_of_pos (by positivity), hzero]
    _ = ∫ t : ℝ, φ t ∂chapter07ConstantFourierMeasure := by
      rw [chapter07ConstantFourierMeasure, integral_smul_measure, integral_dirac]
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]

theorem chapter07_constant_fourier_measure_positive :
    chapter07MeasureTempered chapter07ConstantFourierMeasure ∧
      IsLocallyFiniteMeasure chapter07ConstantFourierMeasure ∧
        chapter07MeasurePositiveOnSchwartz chapter07ConstantFourierMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨2 * Real.pi, 0, ?_, ?_⟩
    · positivity
    · intro R hR
      rw [chapter07ConstantFourierMeasure, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply]
      have hind :
          (Metric.closedBall (0 : ℝ) R).indicator (1 : ℝ → ENNReal) 0 ≤ 1 := by
        by_cases h : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) R <;> simp [h]
      rw [show ENNReal.ofReal (2 * Real.pi * R ^ 0) =
          ENNReal.ofReal (2 * Real.pi) by simp]
      calc
        ENNReal.ofReal (2 * Real.pi) *
              (Metric.closedBall (0 : ℝ) R).indicator (1 : ℝ → ENNReal) 0 ≤
            ENNReal.ofReal (2 * Real.pi) * 1 :=
          mul_le_mul_of_nonneg_left hind (by positivity)
        _ = ENNReal.ofReal (2 * Real.pi) := by simp
  · let : IsFiniteMeasure chapter07ConstantFourierMeasure := by
      unfold chapter07ConstantFourierMeasure
      exact Measure.smul_finite (Measure.dirac 0) ENNReal.ofReal_ne_top
    infer_instance
  · intro φ hφ
    simp only [chapter07ConstantFourierMeasure, integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
    exact smul_nonneg (by positivity) (hφ 0)

theorem chapter07_constant_one_positive_tempered_type :
    chapter07PositiveTemperedType (fun _ : ℝ => 1) := by
  refine ⟨chapter07ConstantFourierMeasure,
    chapter07_constant_one_fourier_representation, ?_⟩
  exact chapter07_constant_fourier_measure_positive

theorem chapter07_stripKernel_endpoint_positive_tempered_type
    (a : ℝ) (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter07PositiveTemperedType (chapter07StripKernel a) := by
  rcases ha with rfl | rfl
  · have heq : chapter07StripKernel (1 / 2 : ℝ) = (fun _ : ℝ => 1) := by
      funext x
      exact chapter07_stripKernel_half x
    rw [heq]
    exact chapter07_constant_one_positive_tempered_type
  · have heq : chapter07StripKernel (-(1 / 2 : ℝ)) = (fun _ : ℝ => 1) := by
      funext x
      exact chapter07_stripKernel_neg_half x
    rw [heq]
    exact chapter07_constant_one_positive_tempered_type

theorem chapter07_stripKernel_endpoint_product_reduces
    (G : Chapter07TestFunction) (a : ℝ)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    (fun x => G x * chapter07StripKernel a x) = G := by
  funext x
  rw [chapter07_stripKernel_endpoint a x ha]
  simp

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
