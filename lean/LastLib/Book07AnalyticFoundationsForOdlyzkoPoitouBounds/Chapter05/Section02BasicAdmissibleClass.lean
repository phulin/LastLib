import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section05DiscriminantAndAnalyticConductor

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

/-! ## 5.2. The basic admissible class -/

theorem chapter05_oneSidedDerivativeBV_iff
    {F : ℝ → ℝ} :
    Chapter05OneSidedDerivativeBV F ↔
      ∃ leftDerivative rightDerivative : ℝ → ℝ,
        (∀ x, HasDerivWithinAt F (leftDerivative x) (Iic x) x) ∧
          (∀ x, HasDerivWithinAt F (rightDerivative x) (Ici x) x) ∧
          BoundedVariationOn leftDerivative univ ∧
            BoundedVariationOn rightDerivative univ := Iff.rfl

/-!
The unit tent is the standard triangular example referred to in §5.2.  The
choice of width one is only a normalization of that example.
-/
def chapter05Triangle (x : ℝ) : ℝ := max (1 - |x|) 0

theorem chapter05_triangle_basically_admissible :
    Chapter05BasicallyAdmissible chapter05Triangle := by
  sorry

theorem chapter05_origin_condition_iff_integrableOn
    {F : ℝ → ℝ} (hContinuous : Continuous F) :
    chapter05OriginCondition F ↔
      IntegrableOn (fun x : ℝ => |1 - F x| / x) (Ioc (0 : ℝ) 1) volume := by
  sorry

theorem chapter05_smooth_even_is_quadratic_at_zero
    {F : ℝ → ℝ} (hEven : Function.Even F) (hF0 : F 0 = 1)
    (hC2 : ContDiffAt ℝ 2 F 0) :
    (fun x : ℝ => 1 - F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) := by
  sorry

theorem chapter05_origin_condition_of_quadratic_bound
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hQuadratic : (fun x : ℝ => 1 - F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2)) :
    chapter05OriginCondition F := by
  sorry

theorem chapter05_smooth_even_origin_condition
    {F : ℝ → ℝ} (hEven : Function.Even F) (hF0 : F 0 = 1)
    (hContinuous : Continuous F) (hC2 : ContDiffAt ℝ 2 F 0) :
    chapter05OriginCondition F := by
  exact chapter05_origin_condition_of_quadratic_bound hContinuous
    (chapter05_smooth_even_is_quadratic_at_zero hEven hF0 hC2)

theorem chapter05_right_corner_is_linear_at_zero
    {F : ℝ → ℝ} (hF0 : F 0 = 1) {d : ℝ}
    (hRightDerivative : HasDerivWithinAt F d (Ici (0 : ℝ)) 0) :
    (fun x : ℝ => 1 - F x) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)] (fun x : ℝ => x) := by
  sorry

theorem chapter05_origin_condition_of_right_linear_bound
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hLinear : (fun x : ℝ => 1 - F x) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
      (fun x : ℝ => x)) :
    chapter05OriginCondition F := by
  sorry

theorem chapter05_right_corner_origin_condition
    {F : ℝ → ℝ} (hF0 : F 0 = 1) (hContinuous : Continuous F) {d : ℝ}
    (hRightDerivative : HasDerivWithinAt F d (Ici (0 : ℝ)) 0) :
    chapter05OriginCondition F := by
  exact chapter05_origin_condition_of_right_linear_bound hContinuous
    (chapter05_right_corner_is_linear_at_zero hF0 hRightDerivative)

theorem chapter05_basically_admissible_vertical_decay
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    chapter05VerticalTransformDecay2 F := by
  sorry

theorem chapter05_basically_admissible_fourier_decay
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖chapter05FourierTransform F t‖ ≤ C / (1 + |t|) ^ 2 := by
  sorry

/-- The convergent sum over the Chapter 4 zero set, weighted by analytic
multiplicity. -/
noncomputable def chapter05SymmetricZeroSum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℂ :=
  ∑' ρ : ℂ,
    (chapter04ZeroMultiplicity K ρ : ℂ) *
      chapter05BilateralLaplaceTransform F ρ

/-- The finite symmetric truncation at height `T`; the zero value for negative
`T` keeps the definition total. -/
noncomputable def chapter05SymmetricZeroPartialSum
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  if _hT : 0 ≤ T then
    Finset.sum (chapter04_zero_band_finite K T).toFinset
      (fun ρ => (chapter04ZeroMultiplicity K ρ : ℂ) *
        chapter05BilateralLaplaceTransform F ρ)
  else 0

theorem chapter05_symmetric_zero_sum_summable
    (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      (chapter04ZeroMultiplicity K ρ : ℂ) *
        chapter05BilateralLaplaceTransform F ρ) := by
  sorry

theorem chapter05_symmetric_zero_sum_converges
    (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Tendsto (chapter05SymmetricZeroPartialSum K F) atTop
      (𝓝 (chapter05SymmetricZeroSum K F)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
