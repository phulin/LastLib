import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07.Section03TheUnconditionalArgument

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

/- Fourier positivity is the condition used for the zero term; pointwise
   positivity is the condition used for the prime-power term. -/
def chapter07PrimePositivityCone : Set Chapter07TestFunction :=
  {f | chapter07PointwiseNonnegative f}

def chapter07ZeroPositivityCone : Set Chapter07TestFunction :=
  {f | chapter07FourierNonnegative f}

def chapter07RequiredPositivityCone : Set Chapter07TestFunction :=
  chapter07PrimePositivityCone ∩ chapter07ZeroPositivityCone

theorem chapter07_mem_requiredPositivityCone_iff (f : Chapter07TestFunction) :
    f ∈ chapter07RequiredPositivityCone ↔
      chapter07PointwiseNonnegative f ∧ chapter07FourierNonnegative f := by
  rfl

def chapter07FinitePrimeContribution
    {α : Type*} (weight : α → ℝ) (known : Finset α) : ℝ :=
  Finset.sum known (fun p => weight p)

theorem chapter07_finitePrimeContribution_nonnegative
    {α : Type*} (weight : α → ℝ) (known : Finset α)
    (hweight : ∀ p, 0 ≤ weight p) :
    0 ≤ chapter07FinitePrimeContribution weight known := by
  sorry

theorem chapter07_finitePrimeContribution_mono
    {α : Type*} (weight : α → ℝ) {known₁ known₂ : Finset α}
    (hknown : known₁ ⊆ known₂) (hweight : ∀ p, 0 ≤ weight p) :
    chapter07FinitePrimeContribution weight known₁ ≤
      chapter07FinitePrimeContribution weight known₂ := by
  sorry

def chapter07WeightedPrimeContribution
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) (known : Finset α) : ℝ :=
  Finset.sum known (fun p => weight p * f (argument p))

theorem chapter07_weightedPrimeContribution_nonnegative
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) (known : Finset α)
    (hf : chapter07PointwiseNonnegative f)
    (hweight : ∀ p, 0 ≤ weight p) :
    0 ≤ chapter07WeightedPrimeContribution f argument weight known := by
  sorry

theorem chapter07_weightedPrimeContribution_mono
    (f : Chapter07TestFunction) {α : Type*}
    (argument weight : α → ℝ) {known₁ known₂ : Finset α}
    (hknown : known₁ ⊆ known₂)
    (hf : chapter07PointwiseNonnegative f)
    (hweight : ∀ p, 0 ≤ weight p) :
    chapter07WeightedPrimeContribution f argument weight known₁ ≤
      chapter07WeightedPrimeContribution f argument weight known₂ := by
  sorry

theorem chapter07_discard_nonnegative_prime_term
    (base prime : ℝ) (hprime : 0 ≤ prime) :
    base - prime ≤ base := by
  sorry

def chapter07Gaussian (σ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * σ ^ 2))

theorem chapter07_gaussian_fourier_nonnegative (σ : ℝ) (hσ : 0 < σ) :
    chapter07FourierNonnegative (chapter07Gaussian σ) := by
  sorry

theorem chapter07_gaussian_is_schwartz (σ : ℝ) (hσ : 0 < σ) :
    ∃ g : SchwartzMap ℝ ℝ, ∀ x, g x = chapter07Gaussian σ x := by
  sorry

theorem chapter07_gaussian_not_compactly_supported (σ : ℝ) (hσ : 0 < σ) :
    ¬HasCompactSupport (chapter07Gaussian σ) := by
  sorry

/- The preceding explicit-formula chapter supplies field-specific prime-power
   weights.  This field-independent predicate records only the
   absolute-convergence interface needed for a noncompact test function. -/
def chapter07PrimeSeriesAbsolutelyConvergent
    (f : Chapter07TestFunction) (weight : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => ‖(weight n : ℝ) * f (Real.log n)‖)

def chapter07GaussianExplicitFormulaHypothesis
    (σ : ℝ) (weight : ℕ → ℝ) : Prop :=
  0 < σ ∧ chapter07PrimeSeriesAbsolutelyConvergent
    (chapter07Gaussian σ) weight

def chapter07Box (T : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ T / 2 then 1 else 0

def chapter07Autocorrelation
    (g : Chapter07TestFunction) (x : ℝ) : ℝ :=
  ∫ y : ℝ, g y * g (y + x)

def chapter07Triangle (T : ℝ) (x : ℝ) : ℝ :=
  max 0 (1 - |x| / T)

theorem chapter07_autocorrelation_positiveType
    (g : Chapter07TestFunction) (hg : Integrable g) :
    chapter07PositiveType (chapter07Autocorrelation g) := by
  sorry

theorem chapter07_triangle_eq_normalized_autocorrelation
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    chapter07Triangle T x =
      (1 / T) * chapter07Autocorrelation (chapter07Box T) x := by
  sorry

theorem chapter07_triangle_positiveType (T : ℝ) (hT : 0 < T) :
    chapter07PositiveType (chapter07Triangle T) := by
  sorry

theorem chapter07_triangle_pointwiseNonnegative (T : ℝ) :
    chapter07PointwiseNonnegative (chapter07Triangle T) := by
  sorry

theorem chapter07_triangle_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (chapter07Triangle T) := by
  sorry

theorem chapter07_triangle_fourier_nonnegative (T : ℝ) (hT : 0 < T) :
    chapter07FourierNonnegative (chapter07Triangle T) := by
  sorry

theorem chapter07_triangle_has_compact_support (T : ℝ) (hT : 0 < T) :
    HasCompactSupport (chapter07Triangle T) := by
  sorry

theorem chapter07_triangle_not_smooth (T : ℝ) (hT : 0 < T) :
    ¬DifferentiableAt ℝ (chapter07Triangle T) 0 := by
  sorry

def chapter07PrimePowerSupport (f : Chapter07TestFunction) : Set ℕ :=
  {n : ℕ | 2 ≤ n ∧ f (Real.log n) ≠ 0}

theorem chapter07_triangle_primePowerSupport_finite
    (T : ℝ) (hT : 0 < T) :
    Set.Finite (chapter07PrimePowerSupport (chapter07Triangle T)) := by
  sorry

/- A smoothing witness records exactly the properties used when the triangle
   is replaced by a smooth certificate in the next chapter. -/
def chapter07SmoothApproximation
    (F H : Chapter07TestFunction) (ε : ℝ) : Prop :=
  ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ Integrable H ∧ chapter07Even H ∧
    chapter07PointwiseNonnegative H ∧ chapter07PositiveType H ∧
    ∀ x, |H x - F x| ≤ ε

theorem chapter07_triangle_smoothing_interface
    (T ε : ℝ) (hT : 0 < T) (hε : 0 < ε) :
    ∃ H : Chapter07TestFunction,
      chapter07SmoothApproximation (chapter07Triangle T) H ε := by
  sorry

def chapter07IntervalBump (T : ℝ) (x : ℝ) : ℝ :=
  if |x| ≤ T then 1 else 0

theorem chapter07_intervalBump_pointwiseNonnegative (T : ℝ) :
    chapter07PointwiseNonnegative (chapter07IntervalBump T) := by
  sorry

theorem chapter07_intervalBump_fourier_oscillates (T : ℝ) (hT : 0 < T) :
    ∃ t : ℝ,
      (chapter07FourierTransform (chapter07IntervalBump T) t).re < 0 := by
  sorry

theorem chapter07_intervalBump_not_fourierNonnegative (T : ℝ) (hT : 0 < T) :
    ¬chapter07FourierNonnegative (chapter07IntervalBump T) := by
  sorry

def chapter07CosineWave (x : ℝ) : ℝ :=
  Real.cos x

theorem chapter07_cosineWave_positiveType :
    chapter07PositiveType chapter07CosineWave := by
  sorry

theorem chapter07_cosineWave_not_pointwiseNonnegative :
    ¬chapter07PointwiseNonnegative chapter07CosineWave := by
  sorry

def chapter07OscillatoryGaussian (σ : ℝ) (x : ℝ) : ℝ :=
  chapter07Gaussian σ x * Real.cos x

theorem chapter07_oscillatoryGaussian_fourierNonnegative
    (σ : ℝ) (hσ : 0 < σ) :
    chapter07FourierNonnegative (chapter07OscillatoryGaussian σ) := by
  sorry

theorem chapter07_oscillatoryGaussian_not_pointwiseNonnegative
    (σ : ℝ) (hσ : 0 < σ) :
    ¬chapter07PointwiseNonnegative (chapter07OscillatoryGaussian σ) := by
  sorry

theorem chapter07_prime_and_zero_positivity_are_independent :
    (∃ f : Chapter07TestFunction,
      chapter07PointwiseNonnegative f ∧ ¬chapter07FourierNonnegative f) ∧
      (∃ f : Chapter07TestFunction,
        chapter07FourierNonnegative f ∧ ¬chapter07PointwiseNonnegative f) := by
  sorry

theorem chapter07_optimization_requires_both_positivity_cones
    (F : Chapter07TestFunction)
    (hprime : F ∈ chapter07PrimePositivityCone)
    (hzero : F ∈ chapter07ZeroPositivityCone) :
    F ∈ chapter07RequiredPositivityCone := by
  exact ⟨hprime, hzero⟩

end
end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter07
