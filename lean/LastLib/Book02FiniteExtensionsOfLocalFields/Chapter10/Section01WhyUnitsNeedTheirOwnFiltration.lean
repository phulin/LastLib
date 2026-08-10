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
  constructor
  · rw [chapter10FieldUnitFiltration, chapter10_unit_filtration_zero]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      rw [ValuationSubring.mem_unitGroup_iff]
      change A.valuation ((Units.map A.subtype.toMonoidHom u : Lˣ)) = 1
      simpa using A.valuation_unit u
    · intro hx
      let x' : A.unitGroup := ⟨x, hx⟩
      refine ⟨A.unitGroupMulEquiv x', trivial, ?_⟩
      apply Units.ext
      change (((A.unitGroupMulEquiv x' : Aˣ) : A) : L) = (x : L)
      exact A.coe_unitGroupMulEquiv_apply x'
  · rw [chapter10FieldUnitFiltration]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [ValuationSubring.mem_principalUnitGroup_iff]
      change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1 at hu
      rw [pow_one] at hu
      exact (ValuationSubring.valuation_lt_one_iff A ((u : A) - 1)).1 hu
    · intro hx
      let x' : A.unitGroup := ⟨x, A.principal_units_le_units hx⟩
      refine ⟨A.unitGroupMulEquiv x', ?_, ?_⟩
      · change ((A.unitGroupMulEquiv x' : Aˣ) : A) - 1 ∈
          (IsLocalRing.maximalIdeal A) ^ 1
        rw [pow_one]
        exact (ValuationSubring.valuation_lt_one_iff A _).2
          (by
            have hx' : A.valuation ((x : L) - 1) < 1 :=
              (ValuationSubring.mem_principalUnitGroup_iff A x).1 hx
            simpa [A.coe_unitGroupMulEquiv_apply x'] using hx')
      · apply Units.ext
        change (((A.unitGroupMulEquiv x' : Aˣ) : A) : L) = (x : L)
        exact A.coe_unitGroupMulEquiv_apply x'

/-- A separated valuation-ring topology makes the unit filtration Hausdorff. -/
theorem chapter10_unit_filtration_separated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hseparated : ∀ x : A,
      (∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A) ^ n) → x = 0) :
    ⨅ n : ℕ, chapter10UnitFiltration A n = ⊥ := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ n : ℕ, u ∈ chapter10UnitFiltration A n := by
      intro n
      exact (Subgroup.mem_iInf.mp hu) n
    have hzero : (u : A) - 1 = 0 := hseparated ((u : A) - 1) (by
      intro n
      exact hu' n)
    simp only [Subgroup.mem_bot]
    apply Units.ext
    change (u : A) = 1
    exact sub_eq_zero.mp hzero
  · intro hu
    simp only [Subgroup.mem_bot] at hu
    subst u
    refine (Subgroup.mem_iInf).2 ?_
    intro n
    exact (chapter10UnitFiltration A n).one_mem

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
