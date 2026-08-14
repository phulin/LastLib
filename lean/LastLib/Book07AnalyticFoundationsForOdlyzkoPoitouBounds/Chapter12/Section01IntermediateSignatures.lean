import Mathlib.Order.ConditionallyCompleteLattice.Finset
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

/- The threshold API makes explicit the positivity of the slope needed for the
   strict upward-threshold comparison. -/

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
  simp [chapter12AffineLogExpression, chapter12AffineLogBase,
    chapter12AffineLogSlope, chapter11ExplicitFormulaLogExpression]
  ring

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
  dsimp [chapter12AffineLogExpression]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hαβ hslope)

def chapter12ContinuousSignatureThreshold
    (n : ℕ) (T U : ℝ) : ℝ :=
  (Real.log U - chapter12AffineLogBase n T) /
    chapter12AffineLogSlope T

theorem chapter12_continuous_signature_threshold_solves
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : chapter12AffineLogSlope T ≠ 0) :
    chapter12AffineLogExpression n T
        (chapter12ContinuousSignatureThreshold n T U) = Real.log U := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  by_cases hnzero : n = 0
  · exact False.elim (hn0 hnzero)
  · by_cases hUzero : U = 0
    · exact False.elim ((ne_of_gt hU) hUzero)
    · simp [chapter12AffineLogExpression, chapter12ContinuousSignatureThreshold, hslope]

theorem chapter12_continuous_signature_threshold_unique
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : chapter12AffineLogSlope T ≠ 0) :
    ∀ α : ℝ,
      chapter12AffineLogExpression n T α = Real.log U ↔
        α = chapter12ContinuousSignatureThreshold n T U := by
  intro α
  constructor
  · intro hα
    have hαmul : α * chapter12AffineLogSlope T =
        Real.log U - chapter12AffineLogBase n T := by
      change chapter12AffineLogBase n T + α * chapter12AffineLogSlope T =
        Real.log U at hα
      linarith
    have hθmul : chapter12ContinuousSignatureThreshold n T U *
        chapter12AffineLogSlope T =
        Real.log U - chapter12AffineLogBase n T := by
      rw [chapter12ContinuousSignatureThreshold, div_mul_cancel₀ _ hslope]
    have hmul : α * chapter12AffineLogSlope T =
        chapter12ContinuousSignatureThreshold n T U * chapter12AffineLogSlope T :=
      hαmul.trans hθmul.symm
    have hzero : (α - chapter12ContinuousSignatureThreshold n T U) *
        chapter12AffineLogSlope T = 0 := by
      calc
        (α - chapter12ContinuousSignatureThreshold n T U) *
            chapter12AffineLogSlope T =
            α * chapter12AffineLogSlope T -
              chapter12ContinuousSignatureThreshold n T U *
                chapter12AffineLogSlope T := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    have hdiff : α - chapter12ContinuousSignatureThreshold n T U = 0 := by
      rcases mul_eq_zero.mp hzero with hdiff | hs
      · exact hdiff
      · exact (hslope hs).elim
    exact sub_eq_zero.mp hdiff
  · intro hα
    rw [hα]
    exact chapter12_continuous_signature_threshold_solves hn hU hslope

theorem chapter12_continuous_signature_threshold_lt_iff
    {n : ℕ} (hn : 0 < n) {T U : ℝ} (hU : 0 < U)
    (hslope : 0 < chapter12AffineLogSlope T) (α : ℝ) :
    Real.log U < chapter12AffineLogExpression n T α ↔
      chapter12ContinuousSignatureThreshold n T U < α := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  by_cases hnzero : n = 0
  · exact False.elim (hn0 hnzero)
  · by_cases hUzero : U = 0
    · exact False.elim ((ne_of_gt hU) hUzero)
    · change Real.log U < chapter12AffineLogBase n T +
        α * chapter12AffineLogSlope T ↔
        (Real.log U - chapter12AffineLogBase n T) /
          chapter12AffineLogSlope T < α
      constructor
      · intro h
        apply (div_lt_iff₀ hslope).2
        linarith
      · intro h
        have h' := (div_lt_iff₀ hslope).1 h
        linarith

def chapter12AdmissibleSignatureRatios (n : ℕ) : Set ℝ :=
  {α | ∃ r₁ : ℕ,
      chapter12AdmissibleSignature n r₁ ∧
        α = (r₁ : ℝ) / (n : ℝ)}

theorem chapter12_admissible_signature_iff_parity
    (n r₁ : ℕ) :
    chapter12AdmissibleSignature n r₁ ↔
      r₁ ≤ n ∧ Even (n - r₁) := by
  constructor
  · rintro ⟨r₂, h⟩
    refine ⟨by omega, ?_⟩
    refine ⟨r₂, ?_⟩
    omega
  · rintro ⟨hle, ⟨r₂, h⟩⟩
    exact ⟨r₂, by omega⟩

theorem chapter12_admissible_signature_ratio_mem
    {n r₁ r₂ : ℕ} (h : r₁ + 2 * r₂ = n) :
    (r₁ : ℝ) / (n : ℝ) ∈ chapter12AdmissibleSignatureRatios n := by
  exact ⟨r₁, ⟨r₂, h⟩, rfl⟩

theorem chapter12_admissible_signature_ratio_mem_Icc
    {n r₁ r₂ : ℕ} (hn : 0 < n) (h : r₁ + 2 * r₂ = n) :
    (r₁ : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · have hr₁ : r₁ ≤ n := by
      omega
    have hn' : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    apply (div_le_iff₀ hn').2
    simpa using (show (r₁ : ℝ) ≤ (n : ℝ) by exact_mod_cast hr₁)

def chapter12RoundedSignatureRatio (n : ℕ) (θ : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ α : ℝ,
        α ∈ chapter12AdmissibleSignatureRatios n ∧ θ < α then
      sInf {α : ℝ | α ∈ chapter12AdmissibleSignatureRatios n ∧ θ < α}
    else θ

theorem chapter12_rounded_signature_ratio_is_next_admissible
    {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hnext : ∃ α : ℝ,
      α ∈ chapter12AdmissibleSignatureRatios n ∧ θ < α) :
    chapter12RoundedSignatureRatio n θ ∈ chapter12AdmissibleSignatureRatios n ∧
      θ < chapter12RoundedSignatureRatio n θ ∧
      ∀ α : ℝ, α ∈ chapter12AdmissibleSignatureRatios n → θ < α →
        chapter12RoundedSignatureRatio n θ ≤ α := by
  classical
  let S : Set ℝ :=
    {α : ℝ | α ∈ chapter12AdmissibleSignatureRatios n ∧ θ < α}
  have hS_nonempty : S.Nonempty := by
    by_cases hnzero : n = 0
    · exact False.elim ((Nat.ne_of_gt hn) hnzero)
    · rcases hnext with ⟨α, hα, hθα⟩
      exact ⟨α, hα, hθα⟩
  have hAfinite : (chapter12AdmissibleSignatureRatios n).Finite := by
    refine (Set.finite_le_nat n).image
        (fun r : ℕ => (r : ℝ) / (n : ℝ)) |>.subset ?_
    rintro α ⟨r₁, ⟨r₂, hsign⟩, rfl⟩
    refine ⟨r₁, ?_, rfl⟩
    change r₁ ≤ n
    change r₁ + 2 * r₂ = n at hsign
    omega
  have hSfinite : S.Finite := by
    refine hAfinite.subset ?_
    intro α hα
    exact hα.1
  have hS_mem : sInf S ∈ S := hS_nonempty.csInf_mem hSfinite
  have hS_gt : θ < sInf S := by
    apply (hSfinite.lt_csInf_iff hS_nonempty).2
    intro α hα
    exact hα.2
  have hS_le : ∀ α : ℝ, α ∈ S → sInf S ≤ α := by
    intro α hα
    exact csInf_le hSfinite.bddBelow hα
  have hratio : chapter12RoundedSignatureRatio n θ = sInf S := by
    simp [chapter12RoundedSignatureRatio, S, hnext]
  rw [hratio]
  exact ⟨hS_mem.1, hS_gt, by
    intro α hα hθα
    exact hS_le α ⟨hα, hθα⟩⟩

theorem chapter12_rounded_signature_ratio_eq_theta_of_no_strictly_larger
    {n : ℕ} {θ : ℝ}
    (hnext : ¬ ∃ α : ℝ,
      α ∈ chapter12AdmissibleSignatureRatios n ∧ θ < α) :
    chapter12RoundedSignatureRatio n θ = θ := by
  simp [chapter12RoundedSignatureRatio, hnext]

noncomputable def chapter12SignatureByDegreeGrid (N : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let candidates := (Finset.range (N + 1)).product (Finset.range (N + 1))
  exact candidates.filter (fun p => chapter12AdmissibleSignature p.1 p.2)

theorem chapter12_signature_grid_mem_of_admissible
    {N n r₁ : ℕ} (hn : n ≤ N)
    (hr₁ : r₁ ≤ N) (hsign : chapter12AdmissibleSignature n r₁) :
    (n, r₁) ∈ chapter12SignatureByDegreeGrid N := by
  classical
  simp [chapter12SignatureByDegreeGrid, hn, hr₁, hsign]

theorem chapter12_field_signature_mem_grid
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} (hdegree : chapter12Degree K ≤ N) :
    (chapter12Degree K, chapter12RealPlaceCount K) ∈
      chapter12SignatureByDegreeGrid N := by
  apply chapter12_signature_grid_mem_of_admissible hdegree
  · have hsign := chapter12_signature_formula K
    omega
  · exact chapter12_field_signature_admissible K

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
  exact (chapter12_real_proportion_eq_one_iff_full_real_signature K).2
    C.upstairs_full_real_signature

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter12
