import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section03PositiveType

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open MeasureTheory

/-! ## 5.4. The two positivity regimes -/

theorem chapter05_unconditionally_admissible_iff
    {F : ℝ → ℝ} :
    Chapter05UnconditionallyAdmissible F ↔
      Chapter05BasicallyAdmissible F ∧
        ∃ witness : ℝ → ℝ,
          (∀ x : ℝ, 0 ≤ witness x) ∧
            Function.Even witness ∧
                Chapter05PositiveType witness ∧
                  (∀ x : ℝ, F x = witness x / Real.cosh (x / 2)) := Iff.rfl

theorem chapter05_grh_admissible_iff
    {F : ℝ → ℝ} :
    Chapter05GRHAdmissible F ↔
      Chapter05BasicallyAdmissible F ∧
        (∀ x : ℝ, 0 ≤ F x) ∧
          (∀ t : ℝ,
            (chapter05FourierTransform F t).im = 0 ∧
              0 ≤ (chapter05FourierTransform F t).re) := by
  constructor
  · intro hF
    exact ⟨hF.basic, hF.pointwiseNonnegative, hF.transformNonnegative⟩
  · intro hF
    exact
      { basic := hF.1
        pointwiseNonnegative := hF.2.1
        transformNonnegative := hF.2.2 }

theorem chapter05_grh_admissible_real_transform_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) :
    ∀ t : ℝ, 0 ≤ chapter05RealFourierTransform F t := by
  intro t
  have hEq := chapter05_fourier_transform_eq_ofReal_real_transform
    (chapter05_basically_admissible_integrable hF.basic) hF.basic.even t
  have hnonneg := (hF.transformNonnegative t).2
  rw [hEq] at hnonneg
  exact hnonneg

theorem chapter05_grh_admissible_central_line_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) (t : ℝ) :
    (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
      0 ≤ (chapter05BilateralLaplaceTransform F
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hEq := chapter05_laplace_on_critical_line
    (chapter05_basically_admissible_integrable hF.basic) hF.basic.even t
  rw [hEq]
  exact hF.transformNonnegative t

theorem chapter05_grh_admissible_lower_bound_admissible
    {F : ℝ → ℝ} (hF : Chapter05GRHAdmissible F) :
    Chapter05LowerBoundAdmissible F := by
  exact ⟨hF.basic, hF.pointwiseNonnegative⟩

/-
DEPENDENCY_GUESS: The later explicit-formula chapter should consume the
central-line statement above together with a `GRH` zero-location predicate;
this chapter intentionally records the transform positivity interface rather
than guessing the number-field zeta API before that chapter is reconciled.
-/

theorem chapter05_unconditionally_admissible_pointwise_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    ∀ x : ℝ, 0 ≤ F x := by
  rcases hF.2 with ⟨witness, hwitness, _, _, hF_eq⟩
  intro x
  rw [hF_eq x]
  exact div_nonneg (hwitness x) (Real.cosh_pos _).le

theorem chapter05_unconditionally_admissible_lower_bound_admissible
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    Chapter05LowerBoundAdmissible F := by
  exact ⟨hF.1, chapter05_unconditionally_admissible_pointwise_nonnegative hF⟩

theorem chapter05_unconditionally_admissible_strip_paired_nonnegative
    {F : ℝ → ℝ} (hF : Chapter05UnconditionallyAdmissible F) :
    chapter05StripPairedNonnegative F := by
  rcases hF.2 with ⟨witness, hwitness, hEven, hPositive, hF_eq⟩
  intro β γ hβ₀ hβ₁
  let a : ℝ := β - 1 / 2
  have ha : |a| ≤ 1 / 2 := by
    rw [abs_le]
    dsimp [a]
    constructor <;> linarith
  have hstrip_even : Function.Even (chapter05StripKernel a) := by
    intro x
    unfold chapter05StripKernel
    rw [show a * -x = -(a * x) by ring, Real.cosh_neg,
      show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  have hprod := chapter05_pair_kernel_positive_type witness a hPositive ha
  have hprod' : Chapter05PositiveType
      (fun x : ℝ => witness x * chapter05StripKernel a x) := by
    simpa [chapter05StripKernel] using hprod
  have hprod_even : Function.Even
      (fun x : ℝ => witness x * chapter05StripKernel a x) := by
    intro x
    change witness (-x) * chapter05StripKernel a (-x) =
      witness x * chapter05StripKernel a x
    rw [hEven x, hstrip_even x]
  have hweighted (b : ℝ) (hb : |b| ≤ 1 / 2) :
      Integrable (fun x : ℝ =>
        (F x : ℂ) * Complex.exp (((b : ℂ) + (γ : ℂ) * Complex.I) * (x : ℂ))) := by
    have hbounded : ∀ x : ℝ, |b| ≤ 1 / 2 →
        (1 / Real.cosh (x / 2)) * Real.exp (b * x) ≤ 2 := by
      intro x hb'
      have hax : b * x ≤ |x| / 2 := by
        calc
          b * x ≤ |b * x| := le_abs_self _
          _ = |b| * |x| := abs_mul _ _
          _ ≤ (1 / 2) * |x| :=
            mul_le_mul_of_nonneg_right hb' (abs_nonneg _)
          _ = |x| / 2 := by ring
      have hexp : Real.exp (b * x) ≤ Real.exp (|x| / 2) :=
        Real.exp_le_exp.mpr hax
      have hcosh : Real.exp (|x| / 2) ≤ 2 * Real.cosh (x / 2) := by
        by_cases hx : 0 ≤ x
        · rw [abs_of_nonneg hx, Real.cosh_eq]
          nlinarith [Real.exp_nonneg (-(x / 2))]
        · have hx' : x ≤ 0 := le_of_not_ge hx
          rw [abs_of_nonpos hx', Real.cosh_eq]
          have hnonneg : 0 ≤ Real.exp (x / 2) := Real.exp_nonneg _
          calc
            Real.exp (-x / 2) = Real.exp (-(x / 2)) := by congr 1; ring
            _ ≤ Real.exp (x / 2) + Real.exp (-(x / 2)) :=
              le_add_of_nonneg_left hnonneg
            _ = 2 * ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) := by ring
      simpa [div_eq_mul_inv, mul_comm] using
        (div_le_iff₀ (Real.cosh_pos _)).2 (hexp.trans hcosh)
    apply Integrable.mono' (hPositive.integrable.norm.const_mul 2)
    · have hFcont : Continuous F := hF.1.continuous
      exact ((Complex.continuous_ofReal.comp hFcont).mul
        (Complex.continuous_exp.comp
          ((continuous_const.add continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_id)))).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : (((b : ℂ) + (γ : ℂ) * Complex.I) * (x : ℂ)).re = b * x := by
        norm_num
      rw [hre, hF_eq x, Real.norm_eq_abs, abs_div,
        abs_of_nonneg (hwitness x), abs_of_pos (Real.cosh_pos _)]
      rw [Real.norm_eq_abs]
      calc
        witness x / Real.cosh (x / 2) * Real.exp (b * x) =
            witness x * ((1 / Real.cosh (x / 2)) * Real.exp (b * x)) := by ring
        _ ≤ witness x * 2 :=
          mul_le_mul_of_nonneg_left (hbounded x hb) (hwitness x)
        _ = 2 * ‖witness x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (hwitness x)]
          ring
  have hI₁ : Integrable (fun x : ℝ =>
      (F x : ℂ) * chapter05LaplaceKernel
        ((β : ℂ) + (γ : ℂ) * Complex.I) x) := by
    change Integrable (fun x : ℝ =>
      (F x : ℂ) *
        Complex.exp (((β : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) *
          (x : ℂ))) volume
    convert hweighted a ha using 1
    funext x
    congr 2
    dsimp [a]
    push_cast
    ring
  have hI₂ : Integrable (fun x : ℝ =>
      (F x : ℂ) * chapter05LaplaceKernel
        (((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I) x) := by
    have hneg : |(-a : ℝ)| ≤ 1 / 2 := by simpa using ha
    change Integrable (fun x : ℝ =>
      (F x : ℂ) *
        Complex.exp (((((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I) -
          (1 / 2 : ℂ)) * (x : ℂ))) volume
    convert hweighted (-a) hneg using 1
    funext x
    congr 2
    dsimp [a]
    push_cast
    ring
  have hpair_eq : chapter05PairedLaplaceTransform F β γ =
      2 * chapter05FourierTransform
        (fun x : ℝ => witness x * chapter05StripKernel a x) (-γ) := by
    unfold chapter05PairedLaplaceTransform
    simp only [chapter05BilateralLaplaceTransform]
    rw [← integral_add hI₁ hI₂]
    calc
      (∫ x : ℝ,
          (F x : ℂ) * chapter05LaplaceKernel
              ((β : ℂ) + (γ : ℂ) * Complex.I) x +
            (F x : ℂ) * chapter05LaplaceKernel
              (((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I) x ∂volume) =
          ∫ x : ℝ, (2 : ℂ) *
            ((witness x * chapter05StripKernel a x : ℝ) : ℂ) *
              Complex.exp (((γ * x : ℝ) : ℂ) * Complex.I) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hF_eq x]
        simp only [chapter05LaplaceKernel]
        have harg₁ :
            ((β : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) * (x : ℂ) =
              ((a : ℂ) * (x : ℂ)) + ((γ * x : ℝ) : ℂ) * Complex.I := by
          dsimp [a]
          push_cast
          ring
        have harg₂ :
            (((1 - β : ℝ) : ℂ) + (γ : ℂ) * Complex.I - (1 / 2 : ℂ)) *
                (x : ℂ) =
              ((-a : ℂ) * (x : ℂ)) + ((γ * x : ℝ) : ℂ) * Complex.I := by
          dsimp [a]
          push_cast
          ring
        rw [harg₁, harg₂, Complex.exp_add, Complex.exp_add]
        rw [show ((a : ℂ) * (x : ℂ)) = ((a * x : ℝ) : ℂ) by
            push_cast; ring,
          show ((-a : ℂ) * (x : ℂ)) = ((-a * x : ℝ) : ℂ) by
            push_cast; ring]
        have hcosh_exp : Real.cosh (a * x) =
            (Real.exp (a * x) + Real.exp (-(a * x))) / 2 := by
          rw [Real.cosh_eq]
        unfold chapter05StripKernel
        rw [hcosh_exp]
        push_cast
        field_simp [Real.cosh_pos (x / 2)]
      _ = 2 * (∫ x : ℝ,
          ((witness x * chapter05StripKernel a x : ℝ) : ℂ) *
            Complex.exp (((γ * x : ℝ) : ℂ) * Complex.I) ∂volume) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = 2 * chapter05FourierTransform
          (fun x : ℝ => witness x * chapter05StripKernel a x) (-γ) := by
        congr 1
        unfold chapter05FourierTransform
        apply integral_congr_ae
        filter_upwards [] with x
        congr 1
        push_cast
        ring_nf
  rw [hpair_eq, chapter05_fourier_transform_neg_eq hprod'.integrable hprod_even γ]
  constructor
  · simp [Complex.mul_im, hprod'.transformNonnegative γ |>.1]
  · simpa [Complex.mul_re] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hprod'.transformNonnegative γ).2)

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
