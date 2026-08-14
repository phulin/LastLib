import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section04PositivityRegimes
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Section01TheConditionalArgument
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Section02TheStripPositiveKernel

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory

def chapter07FOfG (G : Chapter07TestFunction) : Chapter07TestFunction :=
  fun x => G x * chapter07SechHalf x

theorem chapter07FOfG_eq_div_cosh (G : Chapter07TestFunction) :
    chapter07FOfG G = fun x => G x / Real.cosh (x / 2) := by
  funext x
  simp [chapter07FOfG, chapter07SechHalf, div_eq_mul_inv]

abbrev chapter07UnconditionalAdmissible (F : Chapter07TestFunction) : Prop :=
  LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05UnconditionallyAdmissible F

def chapter07PairedZeroContribution
    (G : Chapter07TestFunction) (β γ : ℝ) : ℝ :=
  2 * ∫ x : ℝ,
    G x * chapter07StripKernel (β - 1 / 2) x * Real.cos (γ * x)

theorem chapter07_paired_zero_contribution_formula
    (G : Chapter07TestFunction) (β γ : ℝ)
    (hG : Integrable G) (_heven : chapter07Even G)
    (hβ : |β - 1 / 2| ≤ 1 / 2) :
    (chapter07ZeroTransform (chapter07FOfG G)
        ((β : ℂ) + Complex.I * (γ : ℂ)) +
      chapter07ZeroTransform (chapter07FOfG G)
        (chapter07ZeroPartner ((β : ℂ) + Complex.I * (γ : ℂ)))).re =
      chapter07PairedZeroContribution G β γ := by
  have hbounded : ∀ (a x : ℝ), |a| ≤ 1 / 2 →
      chapter07SechHalf x * Real.exp (a * x) ≤ 2 := by
    intro a x ha
    have hax : a * x ≤ |x| / 2 := by
      calc
        a * x ≤ |a * x| := le_abs_self _
        _ = |a| * |x| := by rw [abs_mul]
        _ ≤ (1 / 2) * |x| := by
          exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ = |x| / 2 := by ring
    have hexp : Real.exp (a * x) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.mpr hax
    have hcosh : Real.exp (|x| / 2) ≤ 2 * Real.cosh (x / 2) := by
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx, Real.cosh_eq]
        have hnonneg : 0 ≤ Real.exp (-(x / 2)) := Real.exp_nonneg _
        nlinarith
      · have hx' : x ≤ 0 := le_of_not_ge hx
        rw [abs_of_nonpos hx', Real.cosh_eq]
        have hnonneg : 0 ≤ Real.exp (x / 2) := Real.exp_nonneg _
        calc
          Real.exp (-x / 2) = Real.exp (-(x / 2)) := by congr 1; ring
          _ ≤ Real.exp (x / 2) + Real.exp (-(x / 2)) :=
            le_add_of_nonneg_left hnonneg
          _ = 2 * ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) := by ring
    rw [chapter07SechHalf]
    calc
      (1 / Real.cosh (x / 2)) * Real.exp (a * x) =
          Real.exp (a * x) / Real.cosh (x / 2) := by ring
      _ ≤ 2 := (div_le_iff₀ (Real.cosh_pos _)).2 (hexp.trans hcosh)
  have hLaplaceIntegrable (a : ℝ) (ha : |a| ≤ 1 / 2) :
      Integrable (fun x : ℝ =>
        (chapter07FOfG G x : ℂ) *
          Complex.exp (((a : ℂ) + Complex.I * (γ : ℂ)) * (x : ℂ))) := by
    have hsechcont : Continuous chapter07SechHalf := by
      unfold chapter07SechHalf
      apply continuous_const.div
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
      intro x
      exact (Real.cosh_pos _).ne'
    have hsechcontC : Continuous (fun x : ℝ => (chapter07SechHalf x : ℂ)) := by
      fun_prop
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (((a : ℂ) + Complex.I * (γ : ℂ)) * (x : ℂ))) := by
      fun_prop
    apply Integrable.mono' (hG.norm.const_mul 2)
    · have hFGmeas : AEStronglyMeasurable
          (fun x : ℝ => (chapter07FOfG G x : ℂ)) := by
        convert hG.ofReal.aestronglyMeasurable.mul hsechcontC.aestronglyMeasurable using 1
        · rfl
        · funext x
          simp [chapter07FOfG]
      exact hFGmeas.mul hcont.aestronglyMeasurable
    · filter_upwards [] with x
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : Complex.re
          (((a : ℂ) + Complex.I * (γ : ℂ)) * (x : ℂ)) = a * x := by
        norm_num
      rw [hre]
      change ‖G x * chapter07SechHalf x‖ * Real.exp (a * x) ≤ 2 * ‖G x‖
      rw [norm_mul, Real.norm_eq_abs]
      have hsech : 0 ≤ chapter07SechHalf x := by
        unfold chapter07SechHalf
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hsech]
      calc
        |G x| * chapter07SechHalf x * Real.exp (a * x) =
            |G x| * (chapter07SechHalf x * Real.exp (a * x)) := by ring
        _ ≤ |G x| * 2 :=
          mul_le_mul_of_nonneg_left (hbounded a x ha) (abs_nonneg _)
        _ = 2 * ‖G x‖ := by rw [Real.norm_eq_abs]; ring
  have ha' : |(1 - β) - 1 / 2| ≤ 1 / 2 := by
    rw [show (1 - β) - 1 / 2 = -(β - 1 / 2) by ring, abs_neg]
    exact hβ
  have hI₁ := hLaplaceIntegrable (β - 1 / 2) hβ
  have hI₂ := hLaplaceIntegrable ((1 - β) - 1 / 2) ha'
  have hpartner :
      chapter07ZeroPartner ((β : ℂ) + Complex.I * (γ : ℂ)) =
        (((1 - β : ℝ) : ℂ) + Complex.I * (γ : ℂ)) := by
    apply Complex.ext <;> simp [chapter07ZeroPartner]
  have hbase₁ :
      (β : ℂ) + Complex.I * (γ : ℂ) - (1 / 2 : ℂ) =
        ((β - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
    norm_num
    ring
  have hbase₂ :
      ((1 - β : ℝ) : ℂ) + Complex.I * (γ : ℂ) - (1 / 2 : ℂ) =
        (((1 - β) - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ) := by
    norm_num
    ring
  have hzero₁ :
      chapter07ZeroTransform (chapter07FOfG G)
          ((β : ℂ) + Complex.I * (γ : ℂ)) =
        ∫ x : ℝ, (chapter07FOfG G x : ℂ) *
          Complex.exp ((((β - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
            (x : ℂ)) := by
    simp only [chapter07ZeroTransform,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hbase₁]
  have hzero₂ :
      chapter07ZeroTransform (chapter07FOfG G)
          (chapter07ZeroPartner ((β : ℂ) + Complex.I * (γ : ℂ))) =
        ∫ x : ℝ, (chapter07FOfG G x : ℂ) *
          Complex.exp (((((1 - β) - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
            (x : ℂ)) := by
    rw [hpartner]
    simp only [chapter07ZeroTransform,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05LaplaceKernel]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hbase₂]
  rw [hzero₁, hzero₂]
  rw [← integral_add hI₁ hI₂]
  calc
    (∫ x : ℝ,
        (chapter07FOfG G x : ℂ) *
            Complex.exp (((((β - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
              (x : ℂ))) +
          (chapter07FOfG G x : ℂ) *
            Complex.exp ((((((1 - β) - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
              (x : ℂ)))).re =
        ∫ x : ℝ,
          ((chapter07FOfG G x : ℂ) *
              Complex.exp (((((β - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
                (x : ℂ))) +
            (chapter07FOfG G x : ℂ) *
              Complex.exp ((((((1 - β) - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) *
                (x : ℂ)))).re :=
      (integral_re (hI₁.add hI₂)).symm
    _ = chapter07PairedZeroContribution G β γ := by
      unfold chapter07PairedZeroContribution
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      have him₁ : Complex.im
          (((((β - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) * (x : ℂ))) =
            γ * x := by
        norm_num
      have him₂ : Complex.im
          ((((((1 - β) - 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)) * (x : ℂ))) =
            γ * x := by
        norm_num
      simp only [chapter07FOfG, Complex.add_re, Complex.mul_re, Complex.exp_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      rw [him₁, him₂]
      have hsumexp :
          Real.exp ((β - 1 / 2) * x) +
              Real.exp (((1 - β) - 1 / 2) * x) =
            2 * Real.cosh ((β - 1 / 2) * x) := by
        rw [show (1 - β) - 1 / 2 = -(β - 1 / 2) by ring,
          show (-(β - 1 / 2)) * x = -((β - 1 / 2) * x) by ring,
          Real.cosh_eq]
        ring
      calc
        _ = G x * chapter07SechHalf x *
              ((Real.exp ((β - 1 / 2) * x) +
                Real.exp (((1 - β) - 1 / 2) * x)) * Real.cos (γ * x)) := by
          ring
        _ = _ := by
          rw [hsumexp]
          simp [chapter07StripKernel, chapter07SechHalf]
          ring

theorem chapter07_pair_kernel_positiveType_strict
    (G : Chapter07TestFunction) (a : ℝ)
    (hG : chapter07PositiveType G) (ha : |a| < 1 / 2) :
    chapter07PositiveType (fun x => G x * chapter07StripKernel a x) := by
  exact chapter07_positiveType_mul G (chapter07StripKernel a) hG
    (chapter07_stripKernel_positiveType a ha)

theorem chapter07_pair_kernel_positiveType_endpoint
    (G : Chapter07TestFunction) (a : ℝ)
    (hG : chapter07PositiveType G)
    (ha : a = (1 / 2 : ℝ) ∨ a = -(1 / 2 : ℝ)) :
    chapter07PositiveType (fun x => G x * chapter07StripKernel a x) := by
  rw [chapter07_stripKernel_endpoint_product_reduces G a ha]
  exact hG

theorem chapter07_paired_zero_contribution_nonnegative
    (G : Chapter07TestFunction) (β γ : ℝ)
    (_hG_integrable : Integrable G) (_hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hβ : |β - 1 / 2| ≤ 1 / 2) :
    0 ≤ chapter07PairedZeroContribution G β γ := by
  have hpaired_fourier
      (hInt : Integrable
        (fun x : ℝ => G x * chapter07StripKernel (β - 1 / 2) x)) :
      chapter07PairedZeroContribution G β γ =
        2 * (chapter07FourierTransform
          (fun x : ℝ => G x * chapter07StripKernel (β - 1 / 2) x) γ).re := by
    rw [chapter07FourierTransform_re_eq_cosineTransform _ hInt γ]
    unfold chapter07PairedZeroContribution chapter07CosineTransform
    apply congrArg (fun r : ℝ => 2 * r)
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  by_cases hstrict : |β - 1 / 2| < 1 / 2
  · have hprod := chapter07_pair_kernel_positiveType_strict G (β - 1 / 2)
      hG_positive hstrict
    have hnonneg := (chapter07_positiveType_fourierNonnegative
      (fun x : ℝ => G x * chapter07StripKernel (β - 1 / 2) x) hprod).2 γ |>.1
    rw [hpaired_fourier hprod.integrable]
    exact mul_nonneg (by norm_num) hnonneg
  · have habs : |β - 1 / 2| = 1 / 2 := by
      exact le_antisymm hβ (le_of_not_gt hstrict)
    have haend : β - 1 / 2 = (1 / 2 : ℝ) ∨
        β - 1 / 2 = -(1 / 2 : ℝ) := by
      by_cases ha : 0 ≤ β - 1 / 2
      · left
        rw [abs_of_nonneg ha] at habs
        linarith
      · right
        have ha' : β - 1 / 2 ≤ 0 := le_of_not_ge ha
        rw [abs_of_nonpos ha'] at habs
        linarith
    have hprod := chapter07_pair_kernel_positiveType_endpoint G (β - 1 / 2)
      hG_positive haend
    have hnonneg := (chapter07_positiveType_fourierNonnegative
      (fun x : ℝ => G x * chapter07StripKernel (β - 1 / 2) x) hprod).2 γ |>.1
    rw [hpaired_fourier hprod.integrable]
    exact mul_nonneg (by norm_num) hnonneg

theorem chapter07_fixed_pair_central_line
    {ρ : ℂ} (hρ : ρ = chapter07ZeroPartner ρ) :
    ρ.re = 1 / 2 := by
  have h := congrArg Complex.re hρ
  simp [chapter07ZeroPartner] at h
  linarith

theorem chapter07_fixed_zero_contribution_nonnegative
    (G : Chapter07TestFunction) (γ : ℝ)
    (_hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G) :
    0 ≤
      (chapter07ZeroTransform (chapter07FOfG G)
        ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))).re := by
  have hprod := chapter07_pair_kernel_positiveType_strict G 0 hG_positive
    (by norm_num : |(0 : ℝ)| < 1 / 2)
  have hFG : Integrable (chapter07FOfG G) := by
    convert hprod.integrable using 1
    funext x
    simp [chapter07FOfG, chapter07StripKernel, chapter07SechHalf]
  have hprod' : chapter07PositiveType (chapter07FOfG G) := by
    convert hprod using 1
    funext x
    simp [chapter07FOfG, chapter07StripKernel, chapter07SechHalf]
  have hevenFG : chapter07Even (chapter07FOfG G) := by
    intro x
    simp only [chapter07FOfG]
    have hsech_even : chapter07SechHalf (-x) = chapter07SechHalf x := by
      simp [chapter07SechHalf, show -x / 2 = -(x / 2) by ring]
    rw [hG_even x, hsech_even]
  have htransform := chapter07_zeroTransform_on_critical_line
    (chapter07FOfG G) hFG hevenFG γ
  rw [htransform]
  exact (chapter07_positiveType_fourierNonnegative
    (chapter07FOfG G) hprod').2 γ |>.1

theorem chapter07_fixed_zero_contribution_is_half_paired
    (G : Chapter07TestFunction) (γ : ℝ)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G) :
      (chapter07ZeroTransform (chapter07FOfG G)
        ((1 / 2 : ℂ) + Complex.I * (γ : ℂ))).re =
      chapter07PairedZeroContribution G (1 / 2 : ℝ) γ / 2 := by
  have hFG : Integrable (chapter07FOfG G) := by
    have hcont : Continuous chapter07SechHalf := by
      unfold chapter07SechHalf
      apply continuous_const.div
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
      intro x
      exact (Real.cosh_pos _).ne'
    apply Integrable.mono' hG_integrable.norm
    · exact hG_integrable.1.mul hcont.aestronglyMeasurable
    · filter_upwards [] with x
      have hsech_nonneg : 0 ≤ chapter07SechHalf x := by
        unfold chapter07SechHalf
        positivity
      have hsech_le : chapter07SechHalf x ≤ 1 := by
        unfold chapter07SechHalf
        rw [div_le_iff₀ (Real.cosh_pos _)]
        simpa only [one_mul] using Real.one_le_cosh (x / 2)
      change ‖G x * chapter07SechHalf x‖ ≤ ‖G x‖
      have hnorm : ‖chapter07SechHalf x‖ = chapter07SechHalf x := by
        rw [Real.norm_eq_abs, abs_of_nonneg hsech_nonneg]
      rw [norm_mul, Real.norm_eq_abs, hnorm]
      exact (mul_le_of_le_one_right (abs_nonneg (G x)) hsech_le)
  have hevenFG : chapter07Even (chapter07FOfG G) := by
    intro x
    simp only [chapter07FOfG]
    have hsech_even : chapter07SechHalf (-x) = chapter07SechHalf x := by
      simp [chapter07SechHalf, show -x / 2 = -(x / 2) by ring]
    rw [hG_even x, hsech_even]
  have htransform := chapter07_zeroTransform_on_critical_line
    (chapter07FOfG G) hFG hevenFG γ
  rw [htransform, chapter07FourierTransform_re_eq_cosineTransform
    (chapter07FOfG G) hFG γ]
  unfold chapter07PairedZeroContribution
  simp only [chapter07StripKernel, one_div]
  ring_nf
  simp only [chapter07FOfG,
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05RealFourierTransform]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.cosh_zero, show x * (1 / 2 : ℝ) = x / 2 by ring,
    show γ * x = x * γ by ring]
  simp only [chapter07SechHalf, one_div, mul_one]

theorem chapter07_unconditional_zero_term_nonnegative
    (Z : Chapter07ZeroSpectrum) (G : Chapter07TestFunction)
    (hG_integrable : Integrable G) (hG_even : chapter07Even G)
    (hG_positive : chapter07PositiveType G)
    (hsum : chapter07ZeroTermConvergent Z (chapter07FOfG G)) :
    0 ≤ chapter07ZeroTerm Z (chapter07FOfG G) := by
  let e : ℂ ≃ ℂ :=
    { toFun := chapter07ZeroPartner
      invFun := chapter07ZeroPartner
      left_inv := chapter07ZeroPartner_involutive
      right_inv := chapter07ZeroPartner_involutive }
  have he : ∀ ρ : ℂ, e ρ = chapter07ZeroPartner ρ := by
    intro ρ
    rfl
  have hpair_nonnegative : ∀ ρ : ℂ,
      0 ≤
        (chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
          chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)).re := by
    intro ρ
    by_cases hρ : ρ ∈ Z.support
    · let β : ℝ := ρ.re
      let γ : ℝ := ρ.im
      have hstrip : |β - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [Z.critical_strip hρ |>.1, Z.critical_strip hρ |>.2]
      have hrepr : ρ = (β : ℂ) + Complex.I * (γ : ℂ) := by
        apply Complex.ext <;> simp [β, γ]
      have hpaired := chapter07_paired_zero_contribution_nonnegative G β γ
        hG_integrable hG_even hG_positive hstrip
      have hformula :
          (chapter07ZeroTransform (chapter07FOfG G) ρ +
            chapter07ZeroTransform (chapter07FOfG G) (e ρ)).re =
            chapter07PairedZeroContribution G β γ := by
        rw [hrepr]
        simpa only [he] using
          (chapter07_paired_zero_contribution_formula G β γ
            hG_integrable hG_even hstrip)
      have hm : Z.multiplicity (e ρ) = Z.multiplicity ρ := by
        rw [he]
        exact Z.multiplicity_partner ρ
      rw [chapter07ZeroTermSummand, chapter07ZeroTermSummand, hm]
      rw [← mul_add]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
      rw [hformula]
      exact mul_nonneg (by positivity) hpaired
    · have hm : Z.multiplicity ρ = 0 := by
        by_contra hm
        exact hρ ((Z.support_iff_multiplicity_ne_zero ρ).2 hm)
      have hm' : Z.multiplicity (e ρ) = 0 := by
        rw [he, Z.multiplicity_partner]
        exact hm
      simp only [chapter07ZeroTermSummand, hm, hm', Nat.cast_zero,
        zero_mul, add_zero, Complex.zero_re, le_refl]
  have hsum' : Summable
      (chapter07ZeroTermSummand Z (chapter07FOfG G)) := hsum
  have hsum_partner : Summable (fun ρ : ℂ =>
      chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)) :=
    hsum'.comp_injective e.injective
  have hsum_pair : Summable (fun ρ : ℂ =>
      chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
        chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)) :=
    hsum'.add hsum_partner
  have hsum_reindexed :
      (∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)) =
        (∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) ρ) := by
    exact e.tsum_eq _
  have hsum_pairs :
      (∑' ρ : ℂ,
        (chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
          chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)).re) =
        2 * (∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) ρ).re := by
    calc
      (∑' ρ : ℂ,
        (chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
          chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)).re) =
          (∑' ρ : ℂ,
            (chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
              chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ))).re :=
        (Complex.re_tsum hsum_pair).symm
      _ = ((∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) ρ) +
          (∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ))).re := by
        rw [hsum'.tsum_add hsum_partner]
      _ = 2 * (∑' ρ : ℂ, chapter07ZeroTermSummand Z (chapter07FOfG G) ρ).re := by
        rw [hsum_reindexed]
        simp only [Complex.add_re]
        ring
  have hnonnegative : 0 ≤
      ∑' ρ : ℂ,
        (chapter07ZeroTermSummand Z (chapter07FOfG G) ρ +
          chapter07ZeroTermSummand Z (chapter07FOfG G) (e ρ)).re :=
    tsum_nonneg hpair_nonnegative
  rw [chapter07ZeroTerm]
  nlinarith [hnonnegative, hsum_pairs]

theorem chapter07_unconditional_zero_term_nonnegative_of_admissible
    (Z : Chapter07ZeroSpectrum) (F : Chapter07TestFunction)
    (hF : chapter07UnconditionalAdmissible F)
    (hsum : chapter07ZeroTermConvergent Z F) :
    0 ≤ chapter07ZeroTerm Z F := by
  obtain ⟨_, witness, _, hw_even, hw_positive, hw_repr⟩ := hF
  have hFeq : F = chapter07FOfG witness := by
    funext x
    rw [chapter07FOfG_eq_div_cosh]
    exact hw_repr x
  have hsumG : chapter07ZeroTermConvergent Z (chapter07FOfG witness) := by
    rw [← hFeq]
    exact hsum
  rw [hFeq]
  exact chapter07_unconditional_zero_term_nonnegative Z witness
    hw_positive.integrable hw_even hw_positive hsumG

theorem chapter07_unconditional_canonical_zero_pair_nonnegative
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) (F : Chapter07TestFunction)
    (hF : LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05UnconditionallyAdmissible F)
    {ρ : ℂ} (hρ : ρ ∈ Z.support) :
    0 ≤
      (LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
          Z F ρ +
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
          Z F (1 - star ρ)).re := by
  let β : ℝ := ρ.re
  let γ : ℝ := ρ.im
  have hβ : 0 ≤ β ∧ β ≤ 1 := by
    simpa [β] using Z.critical_strip hρ
  have hρrepr : ρ = (β : ℂ) + (γ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [β, γ]
  have hpartnerrepr : 1 - star ρ =
      (((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I) := by
    rw [hρrepr]
    apply Complex.ext <;> simp [β, γ]
  have hm : Z.multiplicity (1 - star ρ) = Z.multiplicity ρ := by
    rw [Z.multiplicity_functional_equation_partner (star ρ)]
    exact Z.multiplicity_conjugation_partner ρ
  have hpaired :=
    LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05_unconditionally_admissible_strip_paired_nonnegative
      hF β γ hβ.1 hβ.2
  have htransform :
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06Phi F ρ +
          LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06Phi F
            (1 - star ρ) =
        LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05PairedLaplaceTransform
          F β γ := by
    rw [hpartnerrepr, hρrepr]
    rfl
  simp only [LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand]
  rw [hm, ← mul_add, htransform]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hpaired.2

theorem chapter07_unconditional_canonical_zero_contribution_nonnegative
    (K : Type*) [Field K] [NumberField K]
    (Z : Chapter07CanonicalZeroSpectrum K) (F : Chapter07TestFunction)
    (hF : LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Chapter05UnconditionallyAdmissible F)
    (hsum : Summable (fun ρ : ℂ =>
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroSummand
        Z F ρ)) :
    0 ≤ LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroContribution
      Z F := by
  obtain ⟨_, witness, _, hw_even, hw_positive, hw_repr⟩ := hF
  have hFeq : F = chapter07FOfG witness := by
    funext x
    rw [chapter07FOfG_eq_div_cosh]
    exact hw_repr x
  let Z' := chapter07ZeroSpectrumOfChapter06 K Z
  have hsumG : chapter07ZeroTermConvergent Z' (chapter07FOfG witness) := by
    rw [← hFeq]
    exact hsum
  have hzero : 0 ≤ chapter07ZeroTerm Z' (chapter07FOfG witness) := by
    exact chapter07_unconditional_zero_term_nonnegative Z' witness
      hw_positive.integrable hw_even hw_positive hsumG
  have hzero_eq : chapter07ZeroTerm Z' F =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroContribution
        Z F := by
    rw [chapter07ZeroTerm,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06ZeroContribution,
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.chapter06SymmetricZeroSum]
    congr 1
  rw [← hzero_eq, hFeq]
  exact hzero

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
