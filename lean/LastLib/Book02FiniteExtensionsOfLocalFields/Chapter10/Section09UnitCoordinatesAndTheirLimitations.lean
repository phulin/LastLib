import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section08CompletenessAndInverseLimitsOfUnits

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! ## 10.9. Unit coordinates and their limitations -/

/-- A choice of representatives for the residue field, with zero represented by zero. -/
def Chapter10ResidueRepresentativeSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A → A,
    s 0 = 0 ∧ Function.RightInverse (IsLocalRing.residue A) s

/-- A chosen uniformizer and residue representatives, kept explicit because coordinates depend on them. -/
structure Chapter10UnitCoordinateChoice
    {L : Type*} [Field L] (A : ValuationSubring L) where
  representatives : Chapter10ResidueField A → A
  representatives_zero : representatives 0 = 0
  representatives_rightInverse :
    Function.RightInverse (IsLocalRing.residue A) representatives
  uniformizer : A
  uniformizer_spec : Chapter10Uniformizer A uniformizer

/-- A unit expansion as a convergent product of corrections in successive layers. -/
def Chapter10HasSuccessiveUnitExpansion
    {L : Type*} [Field L] (A : ValuationSubring L) [TopologicalSpace Aˣ]
    (u : Aˣ) : Prop :=
  ∃ s₀ : Aˣ, ∃ c : ℕ → Aˣ,
    Chapter10SuccessiveUnitCorrectionProduct A u s₀ c

/-- Every unit admits a successive-correction expansion after choices are fixed. -/
theorem chapter10_units_have_successive_correction_expansions
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    ∀ u : Aˣ, Chapter10HasSuccessiveUnitExpansion A u := by
  sorry

/-- The coefficientwise logarithm terms `(-1)ⁿ xⁿ⁺¹/(n+1)`. -/
def chapter10LogTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  (-1 : L) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : L)

/-- The coefficientwise exponential terms `xⁿ/n!`. -/
def chapter10ExpTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  x ^ n / ((Nat.factorial n : ℕ) : L)

/-- Convergence predicates for the two formal series. -/
def Chapter10LogSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10LogTerm x)

def Chapter10ExpSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10ExpTerm x)

/-- The abstract group equivalence supplied by convergent logarithm and exponential series. -/
structure Chapter10LogExpLinearization
    {L : Type*} [Field L] (U : Subgroup Lˣ) (I : AddSubgroup L) where
  log : Additive U →+ I
  exp : Multiplicative I →* U
  exp_log : ∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u
  log_exp : ∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x

/-- Deep enough principal units provide a log/exp identification once convergence is established. -/
theorem chapter10_deep_principal_units_log_exp
    {L : Type*} [Field L] (U : Subgroup Lˣ) (I : AddSubgroup L)
    (hseries : ∃ log : Additive U →+ I, ∃ exp : Multiplicative I →* U,
      (∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u) ∧
        (∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x)) :
    Nonempty (Chapter10LogExpLinearization U I) := by
  sorry

/-- The characteristic-free linear part is already the map `1+x ↦ x` on each layer. -/
theorem chapter10_first_order_principal_unit_linearization
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Multiplicative
          (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n) :=
  chapter10_higher_unit_layer_is_additive A n hn

/-- An additive coefficient-field section of reduction. -/
def Chapter10CoefficientFieldSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A →+* A,
    ∀ a, IsLocalRing.residue A (s a) = a

/-- In mixed characteristic, reduction need not have an additive coefficient-field section. -/
theorem chapter10_mixed_characteristic_no_coefficient_field_section
    {L : Type*} [Field L] (A : ValuationSubring L) [CharZero A]
    (p : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p] :
    ¬ Chapter10CoefficientFieldSection A := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
