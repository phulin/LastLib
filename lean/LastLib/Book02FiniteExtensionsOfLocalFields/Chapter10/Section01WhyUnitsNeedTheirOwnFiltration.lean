import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Topology

/-! ## 10.1. Why units need their own filtration -/

/--
For a normalized rank-one discrete valuation, a chosen uniformizer separates
the integer-valued magnitude from the unit in the valuation ring.  The
conclusion is stated both as an explicit factorization and as the resulting
group-coordinate equivalence.
-/
theorem chapter10_valuation_unit_decomposition
    {L Γ₀ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) [Valuation.IsRankOneDiscrete v]
    (π : L) (hπ : v π = Valuation.IsRankOneDiscrete.generator v) :
    (∀ x : L, x ≠ 0 →
      ∃ n : ℤ, ∃ u : v.valuationSubringˣ,
        x = π ^ n * ((u : v.valuationSubring) : L)) ∧
      Nonempty
        (Lˣ ≃* (Multiplicative ℤ × v.valuationSubringˣ)) := by
  sorry

/-- The zeroth congruence subgroup is the full unit group of the valuation ring. -/
theorem chapter10_unit_filtration_zero
    {L : Type*} [Field L] (A : ValuationSubring L) :
    chapter10UnitFiltration A 0 = ⊤ := by
  ext u
  simp [chapter10UnitFiltration, chapter10IdealUnitFiltration]

/-- The product calculation behind closure of `1 + 𝔪ⁿ`. -/
theorem chapter10_unit_product_formula
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ)
    (x y : A) (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (hy : y ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    (1 + x) * (1 + y) = 1 + (x + y + x * y) ∧
      x + y + x * y ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  constructor
  · ring
  · exact add_mem (add_mem hx hy)
      (Ideal.mul_mem_left _ _ hy)

/-- Inverses stay in every congruence subgroup. -/
theorem chapter10_unit_filtration_inverse
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ)
    {u : Aˣ} (hu : u ∈ chapter10UnitFiltration A n) :
    u⁻¹ ∈ chapter10UnitFiltration A n := by
  exact (chapter10UnitFiltration A n).inv_mem hu

/-- The congruence filtration is descending. -/
theorem chapter10_unit_filtration_descending
    {L : Type*} [Field L] (A : ValuationSubring L) :
    ∀ n : ℕ, chapter10UnitFiltration A (n + 1) ≤ chapter10UnitFiltration A n := by
  intro n u hu
  change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hu
  change ((u : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
  exact (Ideal.pow_le_pow_right n.le_succ) hu

/--
The field-level zeroth and first groups agree with the valuation-subring unit
group and Mathlib's principal-unit group, respectively.
-/
theorem chapter10_field_filtration_zero_one
    {L : Type*} [Field L] (A : ValuationSubring L) :
    chapter10FieldUnitFiltration A 0 = A.unitGroup ∧
      chapter10FieldUnitFiltration A 1 = A.principalUnitGroup := by
  sorry

/-- A separated valuation-ring topology makes the unit filtration Hausdorff. -/
theorem chapter10_unit_filtration_separated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hseparated : ∀ x : A,
      (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A) ^ n) → x = 0) :
    ⨅ n : ℕ, chapter10UnitFiltration A n = ⊥ := by
  sorry

/-- The open-subgroup and neighborhood-basis assertion for the unit filtration. -/
theorem chapter10_unit_filtration_is_open_neighborhood_basis
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ]
    (hbasis : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    (∀ n, IsOpen (chapter10UnitFiltration A n : Set Aˣ)) ∧
      ∀ s ∈ 𝓝 (1 : Aˣ), ∃ n,
        (chapter10UnitFiltration A n : Set Aˣ) ⊆ s := by
  exact hbasis

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
