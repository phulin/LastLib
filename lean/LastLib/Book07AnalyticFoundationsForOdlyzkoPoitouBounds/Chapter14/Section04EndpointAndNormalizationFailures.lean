import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

/-! ## 14.4. Endpoint and normalization failures -/

def chapter14UnconditionalAsymptoticLimit (α : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (Real.eulerMascheroniConstant + α)

def chapter14StrictAsymptoticCeilingCondition (U α : ℝ) : Prop :=
  U < chapter14UnconditionalAsymptoticLimit α

theorem chapter14_strict_asymptotic_ceiling_gives_unconditional_degree_cap
    {U α : ℝ} (hU : chapter14StrictAsymptoticCeilingCondition U α)
    (hα : 0 ≤ α) (hα' : α ≤ 1) :
    chapter13HasUnconditionalDegreeCap U α := by
  simpa [chapter14StrictAsymptoticCeilingCondition,
    chapter14UnconditionalAsymptoticLimit] using
    (chapter13_threshold_principle hU hα hα')

theorem chapter14_endpoint_is_not_a_strict_asymptotic_ceiling
    (α : ℝ) :
    ¬ chapter14StrictAsymptoticCeilingCondition
      (chapter14UnconditionalAsymptoticLimit α) α := by
  exact lt_irrefl _

def chapter14StrictRootDiscriminantCeiling
    (K : Type*) [Field K] [NumberField K] (U : ℝ) : Prop :=
  chapter14RootDiscriminant K < U

def chapter14WeakRootDiscriminantCeiling
    (K : Type*) [Field K] [NumberField K] (U : ℝ) : Prop :=
  chapter14RootDiscriminant K ≤ U

theorem chapter14_strict_ceiling_accepts_equal_logarithmic_bound
    (K : Type*) [Field K] [NumberField K] {U : ℝ}
    (hU : 0 < U) (hceil : chapter14StrictRootDiscriminantCeiling K U) :
    ¬ Real.log U ≤ Real.log (chapter14RootDiscriminant K) := by
  sorry

theorem chapter14_weak_ceiling_requires_strict_logarithmic_margin
    (K : Type*) [Field K] [NumberField K] {U L : ℝ}
    (hU : 0 < U) (hceil : chapter14WeakRootDiscriminantCeiling K U)
    (hlower : L ≤ Real.log (chapter14RootDiscriminant K)) :
    ¬ Real.log U < L := by
  sorry

/-! ### Convention audit -/

structure Chapter14NormalizationAudit where
  fourierFrequencyScale : ℝ
  complexCovolumeFactor : ℝ → ℝ
  gammaConstant : ℝ
  completedZetaPoleFactor : ℂ → ℂ

def chapter14CanonicalNormalization : Chapter14NormalizationAudit where
  fourierFrequencyScale := 2 * Real.pi
  complexCovolumeFactor := fun α =>
    Real.rpow (Real.pi / 4) (1 - α)
  gammaConstant := Real.log (8 * Real.pi)
  completedZetaPoleFactor := fun s => s * (s - 1)

def chapter14NormalizationConforms
    (A : Chapter14NormalizationAudit) : Prop :=
  A.fourierFrequencyScale = 2 * Real.pi ∧
    (∀ α : ℝ,
      A.complexCovolumeFactor α = Real.rpow (Real.pi / 4) (1 - α)) ∧
    A.gammaConstant = Real.log (8 * Real.pi) ∧
    (∀ s : ℂ, A.completedZetaPoleFactor s = s * (s - 1))

theorem chapter14_canonical_normalization_conforms :
    chapter14NormalizationConforms chapter14CanonicalNormalization := by
  simp [chapter14NormalizationConforms, chapter14CanonicalNormalization]

theorem chapter14_fourier_frequency_change_inserts_two_pi :
    chapter14CanonicalNormalization.fourierFrequencyScale = 2 * Real.pi :=
  rfl

theorem chapter14_complex_covolume_factor_diagnostic (α : ℝ) :
    chapter14CanonicalNormalization.complexCovolumeFactor α =
      Real.rpow (Real.pi / 4) (1 - α) :=
  rfl

theorem chapter14_gamma_factor_diagnostic :
    chapter14CanonicalNormalization.gammaConstant = Real.log (8 * Real.pi) :=
  rfl

theorem chapter14_completed_zeta_pole_factor_diagnostic (s : ℂ) :
    chapter14CanonicalNormalization.completedZetaPoleFactor s = s * (s - 1) :=
  rfl

def chapter14ExplicitFormulaPolePenalty (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  4 * chapter13A F / (n : ℝ)

def chapter14LogLowerBoundWithPole (F : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    chapter14ExplicitFormulaPolePenalty F n - chapter13B F - α * chapter13C F

def chapter14LogLowerBoundWithoutPole (F : ℝ → ℝ) (_n : ℕ) (α : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + α * (Real.pi / 2) -
    chapter13B F - α * chapter13C F

theorem chapter14_forgetting_pole_factor_removes_pole_penalty
    (F : ℝ → ℝ) (n : ℕ) (α : ℝ) :
    chapter14LogLowerBoundWithPole F n α =
      chapter14LogLowerBoundWithoutPole F n α -
        chapter14ExplicitFormulaPolePenalty F n := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter14
