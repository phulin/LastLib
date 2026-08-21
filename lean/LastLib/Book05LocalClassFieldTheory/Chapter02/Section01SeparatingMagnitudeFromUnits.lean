import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology

/-! ## 2.1. Separating magnitude from units -/

/- `Function.MulExact` records equality of the image of the first map with the
   kernel of the second.  Surjectivity is listed separately because it is the
   final `→ 0` condition in the displayed short exact sequence. -/
structure Chapter02ValuationCoordinateData
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) where
  valuation : Kˣ →* Multiplicative ℤ
  exact : chapter02ValuationExactSequence v valuation

theorem chapter02_valuation_exact_sequence
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) :
    Function.Injective (chapter02UnitInclusion v) ∧
      Function.MulExact (chapter02UnitInclusion v) d.valuation ∧
      Function.Surjective d.valuation := by
  exact d.exact

theorem chapter02_valuation_sequence_is_injective_on_units
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Function.Injective (chapter02UnitInclusion v) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the normalized valuation-coordinate homomorphism is
   supplied by the earlier DVR decomposition interface. -/
theorem chapter02_valuation_coordinate_exists
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hlocal : Chapter02LocalField v) :
    Nonempty (Chapter02ValuationCoordinateData v) := by
  sorry

theorem chapter02_valuation_sequence_splits
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) (π : Kˣ)
    (hπ : d.valuation π = Multiplicative.ofAdd 1) :
    Function.LeftInverse (chapter02UniformizerSection π) d.valuation := by
  intro z
  sorry

theorem chapter02_valuation_unit_decomposition
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (d : Chapter02ValuationCoordinateData v) (π : Kˣ)
    (hπ : d.valuation π = Multiplicative.ofAdd 1)
    (huniformizer : chapter02IsUniformizerUnit v π) :
    (∀ x : K, x ≠ 0 →
      ∃ n : ℤ, ∃ u : Chapter02UnitGroup v,
        x = ((π : Kˣ) : K) ^ n * ((u : Chapter02UnitGroup v) : K)) ∧
      Nonempty
        (Kˣ ≃* (Multiplicative ℤ × Chapter02UnitGroup v)) := by
  sorry

/- The choice of a uniformizer is not canonical.  The following bridge keeps
   the change-of-coordinate statement explicit instead of identifying two
   splittings definitionally. -/
theorem chapter02_uniformizer_change_is_unit_change
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (π π' : Kˣ) (u : Chapter02UnitGroup v)
    (hπ : chapter02IsUniformizerUnit v π)
    (hπ' : chapter02IsUniformizerUnit v π')
    (hchange : (π' : K) = (chapter02UnitInclusion v u : Kˣ) * π) :
    ∀ z : ℤ, ∃ w : Chapter02UnitGroup v,
      ((π' : Kˣ) : K) ^ z =
        ((chapter02UnitInclusion v w : Kˣ) : K) * ((π : Kˣ) : K) ^ z := by
  sorry

theorem chapter02_unit_filtration_zero
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter02UnitFiltration v 0 = ⊤ := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_zero
    (Chapter02ValuationRing v)

theorem chapter02_unit_filtration_mem_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (u : Chapter02UnitGroup v) :
    u ∈ Chapter02UnitFiltration v n ↔
      (u : Chapter02ValuationRing v) - 1 ∈
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n := Iff.rfl

theorem chapter02_mem_valuation_ideal_power_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02ValuationIdealPowerSet v n ↔
      ∃ y : Chapter02ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
          x = (y : K) := Iff.rfl

theorem chapter02_mem_principal_unit_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02PrincipalUnitSet v n ↔
      ∃ y : Chapter02ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
          x = 1 + (y : K) := Iff.rfl

theorem chapter02_mem_field_unit_set_iff
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter02FieldUnitSet v n ↔
      ∃ u : chapter02FieldUnitFiltration v n,
        x = ((u : Kˣ) : K) := Iff.rfl

theorem chapter02_unit_filtration_inverse
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ)
    {u : Chapter02UnitGroup v} (hu : u ∈ Chapter02UnitFiltration v n) :
    u⁻¹ ∈ Chapter02UnitFiltration v n := by
  exact (Chapter02UnitFiltration v n).inv_mem hu

theorem chapter02_unit_filtration_descending
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    ∀ n : ℕ, Chapter02UnitFiltration v (n + 1) ≤
      Chapter02UnitFiltration v n := by
  intro n
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_filtration_descending
    (Chapter02ValuationRing v) n

theorem chapter02_unit_filtration_first_quotient
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Nonempty
      ((Chapter02UnitGroup v ⧸ Chapter02UnitFiltration v 1) ≃*
        (Chapter02ResidueField v)ˣ) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_first_unit_quotient_equiv_residue_units
      (Chapter02ValuationRing v)

theorem chapter02_unit_filtration_higher_quotient
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (hn : 1 ≤ n)
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v)) :
    Nonempty
      ((Chapter02UnitFiltration v n ⧸
          (Chapter02UnitFiltration v (n + 1)).subgroupOf
            (Chapter02UnitFiltration v n)) ≃*
        Multiplicative (Chapter02ResidueField v)) := by
  sorry

theorem chapter02_unit_filtration_is_compact_open
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [UniformSpace (Chapter02UnitGroup v)]
    [IsTopologicalGroup (Chapter02UnitGroup v)]
    [CompleteSpace (Chapter02UnitGroup v)]
    [T2Space (Chapter02UnitGroup v)]
    [Finite (Chapter02ResidueField v)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v))
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    ∀ n : ℕ,
      IsCompact (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) ∧
        IsOpen (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) := by
  sorry

theorem chapter02_unit_group_is_compact
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [UniformSpace (Chapter02UnitGroup v)]
    [IsTopologicalGroup (Chapter02UnitGroup v)]
    [CompleteSpace (Chapter02UnitGroup v)]
    [T2Space (Chapter02UnitGroup v)]
    [Finite (Chapter02ResidueField v)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v))
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    IsCompact (Set.univ : Set (Chapter02UnitGroup v)) := by
  sorry

theorem chapter02_unit_filtration_is_neighborhood_basis
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [TopologicalSpace (Chapter02UnitGroup v)]
    (hbasis : Chapter02UnitFiltrationNeighborhoodBasis v) :
    (∀ n : ℕ,
      IsOpen (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v))) ∧
      ∀ s ∈ 𝓝 (1 : Chapter02UnitGroup v), ∃ n,
        (Chapter02UnitFiltration v n : Set (Chapter02UnitGroup v)) ⊆ s := by
  exact hbasis

theorem chapter02_unit_filtration_separated
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hseparated : ∀ x : Chapter02ValuationRing v,
      (∀ n : ℕ, x ∈
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n) → x = 0) :
    ⨅ n : ℕ, Chapter02UnitFiltration v n = ⊥ := by
  sorry

theorem chapter02_unit_group_inverse_limit
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing v))
      (Chapter02ValuationRing v))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing v)) :
    Nonempty
      (Chapter02UnitGroup v ≃* Chapter02UnitInverseLimit v) := by
  sorry

theorem chapter02_inverse_limit_family_is_transition_compatible
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (x : Chapter02UnitInverseLimit v) (n : ℕ) :
    chapter02PrecisionUnitTransition v n (x.1 (n + 1)) = x.1 n := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
