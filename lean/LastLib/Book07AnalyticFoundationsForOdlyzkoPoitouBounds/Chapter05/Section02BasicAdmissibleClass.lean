import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

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

/-
DEPENDENCY_GUESS: The reconciled Chapter 4 draft should expose the nontrivial
zero enumeration for `ξ_K`, including multiplicity, critical-strip location,
local finiteness, and the unit-band estimate corresponding to (4.4).  This
local interface records only those analytic facts needed to turn the decay
above into convergence; it is intended to be replaced by that earlier API.
-/
structure Chapter05ZeroCountingInterface (D : ℝ) (n : ℕ) where
  discriminantLower : 1 ≤ D
  degreePositive : 0 < n
  zero : ℕ → ℂ
  criticalStrip : ∀ k : ℕ, 0 ≤ (zero k).re ∧ (zero k).re ≤ 1
  locallyFinite : ∀ T : ℝ, 0 ≤ T →
    Set.Finite {k : ℕ | |(zero k).im| ≤ T}
  unitBandBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    ((Set.ncard {k : ℕ |
      T < |(zero k).im| ∧ |(zero k).im| ≤ T + 1} : ℕ) : ℝ) ≤
      C * (Real.log D + (n : ℝ) * Real.log (T + 3))

/-- The convergent sum over an enumeration in which zeros are repeated with
their multiplicities.  Under the local-finiteness/counting interface this is
the value of the symmetric zero sum. -/
noncomputable def chapter05SymmetricZeroSum
    {D : ℝ} {n : ℕ} (Z : Chapter05ZeroCountingInterface D n)
    (F : ℝ → ℝ) : ℂ :=
  ∑' k : ℕ, chapter05BilateralLaplaceTransform F (Z.zero k)

/-- The finite symmetric truncation at height `T`; the zero value for negative
`T` keeps the definition total. -/
noncomputable def chapter05SymmetricZeroPartialSum
    {D : ℝ} {n : ℕ} (Z : Chapter05ZeroCountingInterface D n)
    (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  if hT : 0 ≤ T then
    Finset.sum (Z.locallyFinite T hT).toFinset
      (fun k => chapter05BilateralLaplaceTransform F (Z.zero k))
  else 0

theorem chapter05_symmetric_zero_sum_summable
    {D : ℝ} {n : ℕ} (Z : Chapter05ZeroCountingInterface D n)
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Summable (fun k : ℕ => chapter05BilateralLaplaceTransform F (Z.zero k)) := by
  sorry

theorem chapter05_symmetric_zero_sum_converges
    {D : ℝ} {n : ℕ} (Z : Chapter05ZeroCountingInterface D n)
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Tendsto (chapter05SymmetricZeroPartialSum Z F) atTop
      (𝓝 (chapter05SymmetricZeroSum Z F)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
