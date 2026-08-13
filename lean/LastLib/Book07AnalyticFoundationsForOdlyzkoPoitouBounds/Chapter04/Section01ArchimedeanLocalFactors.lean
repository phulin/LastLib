import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter02
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
open MeasureTheory

/-! ### 4.1. Archimedean local factors -/

/-
The source states these Mellin identities in the convergence half-plane
`0 < Re(s)`.  The definitions in `Dependencies` use the standard
zero-measure convention at the singular point, while the theorem hypotheses
retain the required domain explicitly.
-/
theorem chapter04_real_gaussian_mellin_eq_gamma
    {s : ℂ} (hs : 0 < s.re) :
    chapter04RealGaussianMellin s = chapter04GammaReal s := by
  unfold chapter04RealGaussianMellin chapter04RealGaussianMellinIntegrand
    chapter04GammaReal
  let F : ℝ → ℂ := fun x =>
    Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
      (x : ℂ) ^ s / (x : ℂ)
  have hrewrite :
      (∫ x : ℝ,
        Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
          ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ)) =
        ∫ x : ℝ, F |x| := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [F]
    have hsq : ((|x| : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 := by
      norm_cast
      exact sq_abs x
    rw [hsq]
  rw [hrewrite]
  have heven : (∫ x : ℝ, F |x|) =
      2 * ∫ x : ℝ in Set.Ioi 0, F x := by
    by_cases hf : IntegrableOn (fun x : ℝ => F |x|) (Set.Ioi 0)
    · have hiic : IntegrableOn (fun x : ℝ => F |x|) (Set.Iic 0) := by
        rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
        let m : MeasurableEmbedding fun x : ℝ => -x :=
          (Homeomorph.neg ℝ).measurableEmbedding
        rw [m.integrableOn_map_iff]
        have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic 0 = Set.Ici 0 := by
          ext x
          simp
        rw [hpre]
        simpa [Function.comp_def] using
          (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf)
      calc
        (∫ x : ℝ, F |x|) =
            (∫ x : ℝ in Set.Iic 0, F |x|) +
              ∫ x : ℝ in Set.Ioi 0, F |x| := by
          rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hiic hf,
            Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ]
        _ = 2 * ∫ x : ℝ in Set.Ioi 0, F x := by
          have hposabs :
              (∫ x : ℝ in Set.Ioi 0, F |x|) =
                ∫ x : ℝ in Set.Ioi 0, F x := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
            rw [abs_of_pos hx]
          rw [hposabs, two_mul]
          congr 1
          rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
          refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
          rw [abs_eq_neg_self.mpr hx]
    · have hnot : ¬ Integrable (fun x : ℝ => F |x|) := by
        contrapose hf
        exact hf.integrableOn
      have hposabs :
          (∫ x : ℝ in Set.Ioi 0, F |x|) =
            ∫ x : ℝ in Set.Ioi 0, F x := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        rw [abs_of_pos hx]
      rw [← hposabs, integral_undef hf, integral_undef hnot, mul_zero]
  have hsub :
      (∫ x : ℝ in Set.Ioi 0,
          ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
            ((2 : ℂ)⁻¹ *
              (Complex.exp (-(Real.pi : ℂ) * ((x ^ (2 : ℝ) : ℝ) : ℂ)) *
                (((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (s / 2 - 1))))) =
        ∫ t : ℝ in Set.Ioi 0,
          ((2 : ℂ)⁻¹ *
            (Complex.exp (-(Real.pi : ℂ) * (t : ℂ)) *
              (t : ℂ) ^ (s / 2 - 1)) ) :=
    MeasureTheory.integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ))
      (g := fun t : ℝ =>
        (2 : ℂ)⁻¹ *
          (Complex.exp (-(Real.pi : ℂ) * (t : ℂ)) *
            (t : ℂ) ^ (s / 2 - 1))) (by norm_num)
  have hpoint :
      (∫ x : ℝ in Set.Ioi 0, F x) =
        (∫ x : ℝ in Set.Ioi 0,
          ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
            ((2 : ℂ)⁻¹ *
              (Complex.exp (-(Real.pi : ℂ) * ((x ^ (2 : ℝ) : ℝ) : ℂ)) *
                (((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (s / 2 - 1))))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx'.ne'
    have hxpow :
        (((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (s / 2 - 1)) =
          (x : ℂ) ^ (s - 2) := by
      rw [Real.rpow_two]
      have hsq : ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) * (x : ℂ) := by
        simp [pow_two]
      rw [hsq, Complex.mul_cpow_ofReal_nonneg hx'.le hx'.le]
      rw [← Complex.cpow_add _ _ hxne]
      congr 1
      ring
    rw [hxpow]
    simp only [F]
    rw [Real.rpow_two]
    have hsq : ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 := by
      simp [pow_two]
    rw [hsq]
    have hdiv : (x : ℂ) ^ s / (x : ℂ) = (x : ℂ) ^ (s - 1) := by
      calc
        (x : ℂ) ^ s / (x : ℂ) =
            (x : ℂ) ^ s / (x : ℂ) ^ (1 : ℂ) := by
              rw [Complex.cpow_one]
        _ = (x : ℂ) ^ (s - 1) :=
          (Complex.cpow_sub s 1 hxne).symm
    rw [mul_div_assoc, hdiv]
    have hpow : (x : ℂ) ^ (s - 1) =
        (x : ℂ) * (x : ℂ) ^ (s - 2) := by
      rw [show s - 1 = 1 + (s - 2) by ring,
        Complex.cpow_add _ _ hxne, Complex.cpow_one]
    rw [hpow]
    norm_num [smul_eq_mul]
    ring
  have hpos :
      (∫ x : ℝ in Set.Ioi 0, F x) =
        (2 : ℂ)⁻¹ * (Real.pi : ℂ) ^ (-s / 2) *
          Complex.Gamma (s / 2) := by
    rw [hpoint, hsub]
    rw [MeasureTheory.integral_const_mul]
    convert congrArg (fun z : ℂ => (2 : ℂ)⁻¹ * z)
      (Complex.integral_cpow_mul_exp_neg_mul_Ioi
        (a := s / 2) (r := Real.pi) (by
          norm_num [Complex.div_re]
          linarith) Real.pi_pos) using 1
    · congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [show -(Real.pi : ℂ) * (t : ℂ) =
          -((Real.pi : ℂ) * (t : ℂ)) by ring]
      ring
    · rw [show (1 / Real.pi : ℂ) ^ (s / 2) =
          (Real.pi : ℂ) ^ (-s / 2) by
        rw [show (1 / Real.pi : ℂ) = (Real.pi : ℂ)⁻¹ by
          norm_num]
        rw [Complex.inv_cpow_ofReal_nonneg (le_of_lt Real.pi_pos)]
        simpa [neg_div] using (Complex.cpow_neg (Real.pi : ℂ) (s / 2)).symm
        ]
      ring
  rw [heven, hpos]
  ring

theorem chapter04_complex_gaussian_mellin_eq_gamma
    {s : ℂ} (hs : 0 < s.re) :
    chapter04ComplexGaussianMellin s = chapter04GammaComplex s := by
  unfold chapter04ComplexGaussianMellin chapter04ComplexGaussianMellinIntegrand
    chapter04GammaComplex
  let G : ℝ → ℂ := fun r =>
    (Real.pi : ℂ)⁻¹ *
      Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) * (r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * s - 2)
  have hrewrite :
      (∫ z : ℂ,
        Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) *
            ((‖z‖ ^ 2 : ℝ) : ℂ)) *
          ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
            ((Real.pi : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ))) =
        ∫ z : ℂ, G ‖z‖ := by
    apply MeasureTheory.integral_congr_ae
    refine (volume.ae_ne (0 : ℂ)).mono ?_
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hrne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hsq : ((‖z‖ ^ 2 : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
      simp [pow_two]
    have hpow : ((‖z‖ : ℂ) ^ 2) ^ s =
        (‖z‖ : ℂ) ^ (2 * s) := by
      rw [show (‖z‖ : ℂ) ^ 2 = (‖z‖ : ℂ) * (‖z‖ : ℂ) by ring,
        Complex.mul_cpow_ofReal_nonneg hr.le hr.le]
      rw [← Complex.cpow_add _ _ hrne]
      congr 1
      ring
    have hpowdiv : (‖z‖ : ℂ) ^ (2 * s) /
        (‖z‖ : ℂ) ^ 2 = (‖z‖ : ℂ) ^ (2 * s - 2) := by
      rw [← Complex.cpow_natCast (‖z‖ : ℂ) 2]
      exact (Complex.cpow_sub (2 * s) 2 hrne).symm
    simp only [G]
    rw [hsq, hpow]
    field_simp [hrne, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, hpowdiv]
    rw [show 2 * s = 2 + 2 * (s - 1) by ring,
      Complex.cpow_add _ _ hrne]
    simp
  have hrad :=
    MeasureTheory.integral_fun_norm_addHaar (E := ℂ) (F := ℂ)
      (volume : Measure ℂ) G
  have hdim : Module.finrank ℝ ℂ = 2 := by norm_num
  have hball : volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [MeasureTheory.Measure.real]
  rw [hrewrite]
  rw [hrad, hdim, hball]
  norm_num [G, smul_eq_mul]
  let H : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (s - 1) *
      Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) * (t : ℂ))
  have hsub :
      (∫ y : ℝ in Set.Ioi 0,
          ((2 : ℝ) * y ^ ((2 : ℝ) - 1)) • H (y ^ (2 : ℝ))) =
        ∫ t : ℝ in Set.Ioi 0, H t :=
    MeasureTheory.integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ))
      (g := H) (by norm_num)
  have hpoint :
      (∫ y : ℝ in Set.Ioi 0,
          (2 : ℂ) *
            (Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) *
                ((y ^ 2 : ℝ) : ℂ)) *
              (y : ℂ) * (y : ℂ) ^ (2 * s - 2))) =
        ∫ y : ℝ in Set.Ioi 0,
          ((2 : ℝ) * y ^ ((2 : ℝ) - 1)) • H (y ^ (2 : ℝ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : 0 < y := hy
    have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy'.ne'
    have hsq : ((y ^ (2 : ℝ) : ℝ) : ℂ) = (y : ℂ) ^ 2 := by
      rw [Real.rpow_two]
      simp [pow_two]
    have hpow :
        ((y ^ (2 : ℝ) : ℝ) : ℂ) ^ (s - 1) =
          (y : ℂ) ^ (2 * (s - 1)) := by
      rw [hsq, show (y : ℂ) ^ 2 = (y : ℂ) * (y : ℂ) by ring,
        Complex.mul_cpow_ofReal_nonneg hy'.le hy'.le]
      rw [← Complex.cpow_add _ _ hyne]
      congr 1
      ring
    simp only [H]
    rw [show y ^ ((2 : ℝ) - 1) = y by norm_num [Real.rpow_one], hpow,
      Real.rpow_two]
    rw [show 2 * (s - 1) = 2 * s - 2 by ring]
    rw [Complex.real_smul]
    rw [Complex.ofReal_mul]
    norm_num
    ring
  have hgamma :
      (∫ t : ℝ in Set.Ioi 0, H t) =
        (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s := by
    unfold H
    convert Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := s) (r := 2 * Real.pi) hs (by positivity) using 1
    · congr 1
      funext t
      congr 1
      norm_num
    · rw [one_div, Complex.inv_cpow_ofReal_nonneg (by positivity)]
      rw [Complex.cpow_neg]
      rw [show ((2 * Real.pi : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) by norm_num]
  calc
    2 *
        ((Real.pi : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            (y : ℂ) * ((Real.pi : ℂ)⁻¹ *
              Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) ^ 2)) *
              (y : ℂ) ^ (2 * s - 2))) =
      ∫ y : ℝ in Set.Ioi 0,
        (2 : ℂ) *
          (Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) *
              ((y ^ 2 : ℝ) : ℂ)) *
            (y : ℂ) * (y : ℂ) ^ (2 * s - 2)) := by
      calc
        2 *
            ((Real.pi : ℂ) *
              ∫ y : ℝ in Set.Ioi 0,
                (y : ℂ) * ((Real.pi : ℂ)⁻¹ *
                  Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) ^ 2)) *
                  (y : ℂ) ^ (2 * s - 2))) =
            2 * ∫ y : ℝ in Set.Ioi 0,
                (Real.pi : ℂ) *
                  ((y : ℂ) * ((Real.pi : ℂ)⁻¹ *
                    Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) ^ 2)) *
                    (y : ℂ) ^ (2 * s - 2))) := by
              rw [MeasureTheory.integral_const_mul]
        _ = ∫ y : ℝ in Set.Ioi 0,
                (2 : ℂ) *
                  ((Real.pi : ℂ) *
                    ((y : ℂ) * ((Real.pi : ℂ)⁻¹ *
                      Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) ^ 2)) *
                      (y : ℂ) ^ (2 * s - 2)))) := by
              symm
              exact MeasureTheory.integral_const_mul (μ := volume.restrict (Set.Ioi 0))
                (2 : ℂ) (fun y : ℝ =>
                  (Real.pi : ℂ) *
                    ((y : ℂ) * ((Real.pi : ℂ)⁻¹ *
                      Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) ^ 2)) *
                      (y : ℂ) ^ (2 * s - 2))))
        _ = ∫ y : ℝ in Set.Ioi 0,
                (2 : ℂ) *
                  (Complex.exp (-((2 : ℂ) * (Real.pi : ℂ)) *
                      ((y ^ 2 : ℝ) : ℂ)) *
                    (y : ℂ) * (y : ℂ) ^ (2 * s - 2)) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
              rw [show ((y ^ 2 : ℝ) : ℂ) = (y : ℂ) ^ 2 by simp [pow_two]]
              field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    _ = ∫ y : ℝ in Set.Ioi 0,
          ((2 : ℝ) * y ^ ((2 : ℝ) - 1)) • H (y ^ (2 : ℝ)) := hpoint
    _ = ∫ t : ℝ in Set.Ioi 0, H t := hsub
    _ = (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s := hgamma

theorem chapter04_gamma_real_eq_mathlib
    (s : ℂ) :
    chapter04GammaReal s = Complex.Gammaℝ s := by
  rfl

/-!
Mathlib's Deligne normalization is `Gammaℂ s = 2 * (2π)^(-s) Γ(s)`,
whereas the book fixes `Gamma_C(s) = (2π)^(-s) Γ(s)`.  The factor-two
compatibility is exposed rather than silently identifying the two symbols.
-/
theorem chapter04_gamma_complex_eq_half_mathlib
    (s : ℂ) :
    chapter04GammaComplex s = (2 : ℂ)⁻¹ * Complex.Gammaℂ s := by
  unfold chapter04GammaComplex Complex.Gammaℂ
  ring

theorem chapter04_euler_completed_dedekind_zeta_eq_displayed
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04EulerCompletedDedekindZeta K s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04GammaReal s ^ chapter04RealPlaces K *
          chapter04GammaComplex s ^ chapter04ComplexPlaces K *
            chapter03DedekindZeta K s := by
  simp [chapter04EulerCompletedDedekindZeta, chapter04ArchimedeanFactor, mul_assoc]

theorem chapter04_euler_completed_dedekind_zeta_uses_absolute_discriminant
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04EulerCompletedDedekindZeta K s =
      (chapter02AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s * chapter03DedekindZeta K s := by
  rfl

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
