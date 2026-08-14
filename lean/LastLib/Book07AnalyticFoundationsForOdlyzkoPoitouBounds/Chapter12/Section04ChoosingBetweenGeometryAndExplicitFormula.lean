import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Dependencies
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Section01IntermediateSignatures
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section01TheThresholdFour
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section02TheThresholdThreeSqrtThree
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section03TheThresholdFiveFourthPower
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section04TheTwoPrimeThreshold
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11.Section06QuadraticBaseCertificate

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter09
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open Filter
open scoped Topology

noncomputable section

/-! ## 12.4. Choosing between geometry and the explicit formula -/

def chapter12GeometricRootDiscriminantBound
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter11GeometricRootDiscriminantBound K

def chapter12ExplicitFormulaRootBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  chapter11ExplicitFormulaRootBound K T

def chapter12SafeRootDiscriminantBound
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℝ :=
  max (chapter12GeometricRootDiscriminantBound K)
    (chapter12ExplicitFormulaRootBound K T)

theorem chapter12_geometric_bound_le_safe
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter12GeometricRootDiscriminantBound K ≤
      chapter12SafeRootDiscriminantBound K T := by
  exact le_max_left _ _

theorem chapter12_explicit_bound_le_safe
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    chapter12ExplicitFormulaRootBound K T ≤
      chapter12SafeRootDiscriminantBound K T := by
  exact le_max_right _ _

theorem chapter12_safe_bound_le_root_discriminant
    (K : Type*) [Field K] [NumberField K]
    {T : ℝ} (hT : 0 < T) :
    chapter12SafeRootDiscriminantBound K T ≤ chapter11RootDiscriminant K := by
  exact max_le
    (chapter11_geometric_root_discriminant_bound K)
    (chapter11_explicit_formula_root_discriminant_bound K T hT)

def chapter12GeometryWins
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Prop :=
  chapter12ExplicitFormulaRootBound K T ≤
    chapter12GeometricRootDiscriminantBound K

def chapter12ExplicitFormulaWins
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Prop :=
  chapter12GeometricRootDiscriminantBound K ≤
    chapter12ExplicitFormulaRootBound K T

theorem chapter12_safe_bound_eq_geometry_of_geometry_wins
    (K : Type*) [Field K] [NumberField K] {T : ℝ}
    (h : chapter12GeometryWins K T) :
    chapter12SafeRootDiscriminantBound K T =
      chapter12GeometricRootDiscriminantBound K := by
  exact max_eq_left h

theorem chapter12_safe_bound_eq_explicit_of_explicit_wins
    (K : Type*) [Field K] [NumberField K] {T : ℝ}
    (h : chapter12ExplicitFormulaWins K T) :
    chapter12SafeRootDiscriminantBound K T =
      chapter12ExplicitFormulaRootBound K T := by
  exact max_eq_right h

def chapter12GeometricAsymptoticConstant : ℝ :=
  (Real.pi / 4) * Real.exp 2

def chapter12UnconditionalAsymptoticConstant (α : ℝ) : ℝ :=
  chapter09UnconditionalAsymptoticConstant α

/- LOCAL_DEPENDENCY_GUESS: the factorial-factor limit used by the phrase
   “geometric limit” is the Stirling consequence Mₙ → e².  Chapter 11 has
   the finite factor and its monotonicity, but not this asymptotic bridge. -/
theorem chapter12_minkowski_factor_tendsto_exp_two :
    Tendsto (fun n : ℕ => chapter11MinkowskiFactor n) atTop (𝓝 (Real.exp 2)) := by
  sorry

theorem chapter12_geometric_worst_signature_factor_tendsto :
    Tendsto
      (fun n : ℕ => (Real.pi / 4) * chapter11MinkowskiFactor n)
      atTop (𝓝 chapter12GeometricAsymptoticConstant) := by
  sorry

theorem chapter12_explicit_unconditional_asymptotic_constant_larger
    {α : ℝ} (hα : 0 ≤ α) :
    chapter12GeometricAsymptoticConstant <
      chapter12UnconditionalAsymptoticConstant α := by
  sorry

theorem chapter12_independent_factorial_certificates :
    (4 : ℝ) < (Real.pi / 4) * chapter11MinkowskiFactor 12 ∧
      chapter11ThreeSqrtThreeCeiling <
        (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  exact ⟨chapter11_minkowski_factor_twelve_crosses_four_lower_endpoint,
    chapter11_three_sqrt_three_minkowski_crossing⟩

theorem chapter12_five_fourth_has_no_factorial_crossing
    {n : ℕ} (hn : 0 < n) :
    chapter11MinkowskiFactor n < chapter11FiveFourthCeiling := by
  exact chapter11_minkowski_never_crosses_five_fourth hn

theorem chapter12_five_fourth_requires_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11FiveFourthCeiling) :
    chapter11Degree K ≤ 16 := by
  exact chapter11_five_fourth_degree_cutoff K hceiling

theorem chapter12_two_prime_requires_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11TwoPrimeCeiling) :
    chapter11Degree K ≤ 20 := by
  exact chapter11_two_prime_degree_cutoff K hceiling

theorem chapter12_two_prime_has_no_degree_fifty_three_factorial_crossing :
    ¬ chapter11TwoPrimeCeiling <
      (Real.pi / 4) * chapter11MinkowskiFactor 53 := by
  exact chapter11_two_prime_ceiling_does_not_cross_degree_fifty_three_minkowski

theorem chapter12_smaller_three_sqrt_three_has_two_prime_explicit_cap
    (K : Type*) [Field K] [NumberField K]
    (hceiling : chapter11RootDiscriminant K < chapter11ThreeSqrtThreeCeiling) :
    chapter11Degree K ≤ 20 ∧ chapter11Degree K ≤ 52 := by
  exact ⟨chapter11_three_sqrt_three_explicit_formula_degree_cutoff K hceiling,
    chapter11_minkowski_degree_fifty_three_cutoff K hceiling⟩

def chapter12UnconditionalInfiniteDegreeLogExpression
    (T α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) +
      α * (Real.pi / 2) - chapter11B T - α * chapter11C T

def chapter12UnconditionalFiniteDegreeLogExpression
    (n : ℕ) (T α : ℝ) : ℝ :=
  chapter12AffineLogExpression n T α

def chapter12UnconditionalFiniteDegreeDeficit
    (n : ℕ) (T : ℝ) : ℝ :=
  2 * T / (n : ℝ)

theorem chapter12_unconditional_finite_degree_deficit_exact
    (n : ℕ) (T α : ℝ) :
    chapter12UnconditionalInfiniteDegreeLogExpression T α -
        chapter12UnconditionalFiniteDegreeLogExpression n T α =
      chapter12UnconditionalFiniteDegreeDeficit n T := by
  sorry

def chapter12UnconditionalLimitingLogExpression (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) - Real.log 2 + α

theorem chapter12_unconditional_limiting_log_expression_eq_log_constant
    (α : ℝ) :
    chapter12UnconditionalLimitingLogExpression α =
      Real.log (chapter12UnconditionalAsymptoticConstant α) := by
  sorry

def chapter12UnconditionalArchimedeanDeficit (T α : ℝ) : ℝ :=
  chapter12UnconditionalLimitingLogExpression α -
    chapter12UnconditionalInfiniteDegreeLogExpression T α

/- LOCAL_DEPENDENCY_GUESS: these are the analytic limits proved upstream by
   the exact archimedean formulas.  They are stated here as a bridge because
   the current Chapter 11 dependency file exposes B and C but not their
   limiting theorems. -/
theorem chapter12_unconditional_B_tendsto :
    Tendsto chapter11B atTop (𝓝 (Real.log 2)) := by
  sorry

theorem chapter12_unconditional_C_tendsto :
    Tendsto chapter11C atTop (𝓝 (Real.pi / 2 - 1)) := by
  sorry

theorem chapter12_unconditional_archimedean_deficit_tendsto_zero
    (α : ℝ) :
    Tendsto (fun T : ℝ => chapter12UnconditionalArchimedeanDeficit T α)
      atTop (𝓝 0) := by
  sorry

theorem chapter12_unconditional_archimedean_deficit_inverse_linear
    (α : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 < T₀ ∧
      ∀ T, T₀ ≤ T →
        |chapter12UnconditionalArchimedeanDeficit T α| ≤ C / T := by
  sorry

def chapter12CrudeFiniteDegreeScale (n : ℕ) (T : ℝ) : ℝ :=
  2 * T / (n : ℝ)

def chapter12CrudeArchimedeanScale (T : ℝ) : ℝ :=
  1 / T

def chapter12CrudeBalanceScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / 2)

theorem chapter12_crude_balance_scale_eq
    {n : ℕ} (hn : 0 < n) :
    chapter12CrudeFiniteDegreeScale n (chapter12CrudeBalanceScale n) =
      chapter12CrudeArchimedeanScale (chapter12CrudeBalanceScale n) := by
  sorry

def chapter12GRHPoleCost (n : ℕ) (T : ℝ) : ℝ :=
  4 * chapter09GRHPoleIntegral T / (n : ℝ)

def chapter12GRHExponentialPoleScale (n : ℕ) (T : ℝ) : ℝ :=
  Real.exp (T / 2) / ((n : ℝ) * T)

def chapter12GRHArchimedeanLoss (T α : ℝ) : ℝ :=
  chapter09GRHBT T + α * chapter09GRHCT T

theorem chapter12_grh_pole_integral_exact
    {T : ℝ} (hT : 0 < T) :
    chapter09GRHPoleIntegral T = 4 / T * (Real.cosh (T / 2) - 1) := by
  exact chapter09_grh_pole_integral hT

theorem chapter12_unconditional_pole_integral_exact
    {T : ℝ} (hT : 0 < T) :
    chapter09UnconditionalPoleIntegral T = T / 2 := by
  exact chapter09_unconditional_pole_integral hT

theorem chapter12_grh_pole_cost_has_exponential_over_nT_scale
    {n : ℕ} (hn : 0 < n) :
    ∃ c₁ c₂ T₀ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < T₀ ∧
      ∀ T, T₀ ≤ T →
        c₁ * chapter12GRHExponentialPoleScale n T ≤
            chapter12GRHPoleCost n T ∧
          chapter12GRHPoleCost n T ≤
            c₂ * chapter12GRHExponentialPoleScale n T := by
  sorry

def chapter12ExponentialDecay (f : ℝ → ℝ) : Prop :=
  ∃ C ρ T₀ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ 0 < T₀ ∧
    ∀ T, T₀ ≤ T → |f T| ≤ C * Real.exp (-ρ * T)

def chapter12InverseLinearDecay (f : ℝ → ℝ) : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 < T₀ ∧
    ∀ T, T₀ ≤ T → |f T| ≤ C / T

theorem chapter12_grh_archimedean_losses_tendsto_zero :
    Tendsto chapter09GRHBT atTop (𝓝 0) ∧
      Tendsto chapter09GRHCT atTop (𝓝 0) := by
  exact ⟨chapter09_grh_archimedean_B_tendsto,
    chapter09_grh_archimedean_C_tendsto⟩

theorem chapter12_grh_archimedean_loss_tendsto_zero
    (α : ℝ) :
    Tendsto (fun T : ℝ => chapter12GRHArchimedeanLoss T α)
      atTop (𝓝 0) := by
  sorry

theorem chapter12_grh_B_has_standard_decay :
    chapter12ExponentialDecay chapter09GRHBT ∨
      chapter12InverseLinearDecay chapter09GRHBT := by
  sorry

theorem chapter12_grh_C_has_standard_decay :
    chapter12ExponentialDecay chapter09GRHCT ∨
      chapter12InverseLinearDecay chapter09GRHCT := by
  sorry

def chapter12GRHLogarithmicSupportScale (n : ℕ) : ℝ :=
  if 1 < n then 2 * Real.log (n : ℝ) else 0

theorem chapter12_grh_useful_support_scale_is_logarithmic :
    Tendsto
      (fun n : ℕ =>
        if 1 < n then
          chapter12GRHLogarithmicSupportScale n / Real.log (n : ℝ)
        else 0)
      atTop (𝓝 2) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
