import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter11
open NumberField
open Set
open scoped BigOperators

noncomputable section

/-! ## 12.1. Intermediate signatures -/

def chapter12AffineLogBase (n : ℕ) (T : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
    2 * T / (n : ℝ) - chapter11B T

def chapter12AffineLogSlope (T : ℝ) : ℝ :=
  Real.pi / 2 - chapter11C T

def chapter12AffineLogExpression (n : ℕ) (T α : ℝ) : ℝ :=
  chapter12AffineLogBase n T + α * chapter12AffineLogSlope T

/- SOURCE_ISSUE (books/007-analytic-foundations-for-odlyzko-poitou-bounds.md:§12.1):
   “To exclude a degree at ceiling U, solve (12.1) for α.”  This requires
   π/2 − C_T ≠ 0, and the upward-threshold formulation requires it to be
   positive.  The threshold declarations below expose that hypothesis. -/

theorem chapter12_affine_log_expression_formula
    (n : ℕ) (T α : ℝ) :
    chapter12AffineLogExpression n T α =
      Real.eulerMascheroniConstant + Real.log (8 * Real.pi) -
        2 * T / (n : ℝ) - chapter11B T +
          α * (Real.pi / 2 - chapter11C T) :=
  rfl

theorem chapter12_affine_log_expression_eq_chapter11
    (n : ℕ) (T α : ℝ) :
    chapter12AffineLogExpression n T α =
      chapter11ExplicitFormulaLogExpression n T α := by
  sorry

theorem chapter12_affine_log_expression_decomposition
    (n : ℕ) (T α : ℝ) :
    chapter12AffineLogExpression n T α =
      chapter12AffineLogBase n T + α * chapter12AffineLogSlope T :=
  rfl

theorem chapter12_affine_log_expression_mono_signature
    {n : ℕ} {T α β : ℝ} (hαβ : α ≤ β)
    (hslope : 0 ≤ chapter12AffineLogSlope T) :
    chapter12AffineLogExpression n T α ≤
      chapter12AffineLogExpression n T β := by
  sorry

def chapter12ContinuousSignatureThreshold
    (n : ℕ) (T U : ℝ) : ℝ :=
  (Real.log U - chapter12AffineLogBase n T) /
    chapter12AffineLogSlope T

theorem chapter12_continuous_signature_threshold_solves
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : chapter12AffineLogSlope T ≠ 0) :
    chapter12AffineLogExpression n T
        (chapter12ContinuousSignatureThreshold n T U) = Real.log U := by
  sorry

theorem chapter12_continuous_signature_threshold_unique
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : chapter12AffineLogSlope T ≠ 0) :
    ∀ α : ℝ,
      chapter12AffineLogExpression n T α = Real.log U ↔
        α = chapter12ContinuousSignatureThreshold n T U := by
  sorry

theorem chapter12_continuous_signature_threshold_lt_iff
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : 0 < chapter12AffineLogSlope T) (α : ℝ) :
    Real.log U < chapter12AffineLogExpression n T α ↔
      chapter12ContinuousSignatureThreshold n T U < α := by
  sorry

def chapter12AdmissibleSignatureRatios (n : ℕ) : Set ℝ :=
  {α | ∃ r₁ : ℕ,
      chapter12AdmissibleSignature n r₁ ∧
        α = (r₁ : ℝ) / (n : ℝ)}

theorem chapter12_admissible_signature_iff_parity
    (n r₁ : ℕ) :
    chapter12AdmissibleSignature n r₁ ↔
      r₁ ≤ n ∧ Even (n - r₁) := by
  sorry

theorem chapter12_admissible_signature_ratio_mem
    {n r₁ r₂ : ℕ} (h : r₁ + 2 * r₂ = n) :
    (r₁ : ℝ) / (n : ℝ) ∈ chapter12AdmissibleSignatureRatios n := by
  exact ⟨r₁, ⟨r₂, h⟩, rfl⟩

theorem chapter12_admissible_signature_ratio_mem_Icc
    {n r₁ r₂ : ℕ} (hn : 0 < n) (h : r₁ + 2 * r₂ = n) :
    (r₁ : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

def chapter12RoundedSignatureRatio (n : ℕ) (θ : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ α : ℝ,
        α ∈ chapter12AdmissibleSignatureRatios n ∧ θ ≤ α then
      sInf {α : ℝ | α ∈ chapter12AdmissibleSignatureRatios n ∧ θ ≤ α}
    else θ

theorem chapter12_rounded_signature_ratio_is_next_admissible
    {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ : θ ≤ 1) :
    chapter12RoundedSignatureRatio n θ ∈ chapter12AdmissibleSignatureRatios n ∧
      θ ≤ chapter12RoundedSignatureRatio n θ ∧
      ∀ α : ℝ, α ∈ chapter12AdmissibleSignatureRatios n → θ ≤ α →
        chapter12RoundedSignatureRatio n θ ≤ α := by
  sorry

noncomputable def chapter12SignatureByDegreeGrid (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let candidates := (Finset.range (N + 1)).product (Finset.range (N + 1))
  exact candidates.filter (fun p => chapter12AdmissibleSignature p.1 p.2)

theorem chapter12_signature_grid_mem_of_admissible
    {N n r₁ : ℕ} (hn : n ≤ N)
    (hr₁ : r₁ ≤ N) (hsign : chapter12AdmissibleSignature n r₁) :
    (n, r₁) ∈ chapter12SignatureByDegreeGrid N := by
  sorry

theorem chapter12_field_signature_mem_grid
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} (hdegree : chapter12Degree K ≤ N) :
    (chapter12Degree K, chapter12RealPlaceCount K) ∈
      chapter12SignatureByDegreeGrid N := by
  sorry

/-
The ratio used in a bound is the signature of the field being bounded.  In
particular, total reality of a base field is not an upstairs signature
hypothesis.  The following context makes the two pieces of data explicit;
downstream bounds should use `upstairs_full_real_signature`, or an
`IsTotallyReal K` instance, rather than infer it from the base.
-/
structure Chapter12TotallyRealBaseExtensionContext
    (F K : Type*) [Field F] [Field K]
    [Algebra ℚ F] [FiniteDimensional ℚ F]
    [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [NumberField K] where
  base_totally_real : IsTotallyReal F
  upstairs_full_real_signature : chapter12FullRealSignature K

theorem chapter12_upstairs_alpha_one_of_context
    {F K : Type*} [Field F] [Field K]
    [Algebra ℚ F] [FiniteDimensional ℚ F]
    [Algebra F K] [Algebra ℚ K] [IsScalarTower ℚ F K] [NumberField K]
    (C : Chapter12TotallyRealBaseExtensionContext F K) :
    chapter12RealProportion K = 1 := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
