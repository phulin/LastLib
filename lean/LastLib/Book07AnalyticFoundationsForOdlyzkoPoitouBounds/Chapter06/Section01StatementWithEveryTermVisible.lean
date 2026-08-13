import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06

noncomputable section

open MeasureTheory Set NumberField
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-! ### 6.1. Statement with every term visible -/

@[simp] theorem chapter06_degree_def :
    chapter06Degree K = Module.finrank ℚ K :=
  rfl

@[simp] theorem chapter06_real_places_def :
    chapter06RealPlaces K = NumberField.InfinitePlace.nrRealPlaces K :=
  rfl

@[simp] theorem chapter06_complex_places_def :
    chapter06ComplexPlaces K = NumberField.InfinitePlace.nrComplexPlaces K :=
  rfl

@[simp] theorem chapter06_absolute_discriminant_def :
    chapter06AbsoluteDiscriminant K = |(NumberField.discr K : ℝ)| :=
  rfl

theorem chapter06_signature_degree :
    chapter06RealPlaces K + 2 * chapter06ComplexPlaces K = chapter06Degree K := by
  exact NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

theorem chapter06_absolute_discriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter06AbsoluteDiscriminant K := by
  sorry

theorem chapter06_root_discriminant_eq_canonical
    (K : Type*) [Field K] [NumberField K] :
    chapter06RootDiscriminant K = NumberField.rootDiscr K := by
  sorry

@[simp] theorem chapter06_phi_eq_centered_laplace
    (F : ℝ → ℝ) (s : ℂ) :
    chapter06Phi F s =
      LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.chapter05BilateralLaplaceTransform
        F s :=
  rfl

theorem chapter06_basic_admissible_integrals_convergent
    {F : ℝ → ℝ} (hF : Chapter06BasicallyAdmissible F) :
    IntegrableOn (fun x : ℝ => F x * Real.cosh (x / 2)) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.sinh (x / 2))) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (1 - F x) / (2 * Real.cosh (x / 2))) (Ioi 0) := by
  sorry

theorem chapter06_zero_contribution_is_real
    {K : Type*} [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    (chapter06SymmetricZeroSum P.zeros F).im = 0 := by
  sorry

theorem chapter06_prime_power_support_finite
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    (chapter06PrimePowerSupport (K := K) F).Finite := by
  sorry

noncomputable def chapter06PrimePowerLedger
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ)
    (hF : Chapter06BasicallyAdmissible F) : Finset (Chapter06PrimePower K) :=
  (chapter06_prime_power_support_finite K hF).toFinset

theorem chapter06_mem_prime_power_ledger_iff
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) (q : Chapter06PrimePower K) :
    q ∈ chapter06PrimePowerLedger K F hF ↔
      chapter06PrimePowerTerm F q ≠ 0 := by
  sorry

theorem chapter06_prime_contribution_eq_ledger_sum
    (K : Type*) [Field K] [NumberField K] {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    chapter06PrimeContribution K F =
      2 * ∑ q ∈ chapter06PrimePowerLedger K F hF,
        chapter06PrimePowerTerm F q := by
  sorry

theorem chapter06_prime_contribution_eq_nested_sum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ)
    (hF : Chapter06BasicallyAdmissible F) :
    chapter06PrimeContribution K F =
      2 * ∑' P : Chapter06PrimeIdeal K,
        ∑' m : Chapter06PositiveExponent, chapter06PrimePowerTerm F (P, m) := by
  sorry

/-
DEPENDENCY_GUESS: the absent Chapter 4 draft supplies the canonical
`Chapter06ZetaAnalyticPackage`; the explicit formula below is stated with
that package as an explicit input until the global reconciliation pass can
replace it by the earlier completed-zeta API.
-/
theorem chapter06_weil_poitou_explicit_formula
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Real.log (chapter06AbsoluteDiscriminant K) =
      chapter06ExplicitFormulaRightHandSide K P.zeros F := by
  sorry

theorem chapter06_weil_poitou_explicit_formula_expanded
    (K : Type*) [Field K] [NumberField K]
    (P : Chapter06ZetaAnalyticPackage K) {F : ℝ → ℝ}
    (hF : Chapter06BasicallyAdmissible F) :
    Real.log (chapter06AbsoluteDiscriminant K) =
      (chapter06Degree K : ℝ) *
          (Real.eulerMascheroniConstant + Real.log (8 * Real.pi)) +
        (chapter06RealPlaces K : ℝ) * (Real.pi / 2) -
        4 * chapter06A F -
        (chapter06Degree K : ℝ) * chapter06B F -
        (chapter06RealPlaces K : ℝ) * chapter06C F +
        chapter06ZeroContribution P.zeros F + chapter06PrimeContribution K F := by
  exact chapter06_weil_poitou_explicit_formula K P hF

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter06
