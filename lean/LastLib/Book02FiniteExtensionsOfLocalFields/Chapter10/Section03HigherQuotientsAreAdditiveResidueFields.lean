import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section02TheFirstQuotient

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing

/-! ## 10.3. Higher quotients are additive residue fields -/

/-- The canonical higher layer is an additive group viewed multiplicatively. -/
theorem chapter10_higher_unit_layer_is_additive
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Multiplicative (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n) := by
  sorry

/-- The error in multiplying `1+x` and `1+y` is one layer deeper. -/
theorem chapter10_higher_layer_multiplication_linearizes
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    (x y : A)
    (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n)
    (hy : y ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    x * y ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) ∧
      (1 + x) * (1 + y) - (1 + (x + y)) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
  sorry

/-- Multiplication by a residue scalar on the `n`th additive layer. -/
def chapter10ResiduePowerScaling
    {L : Type*} [Field L] (A : ValuationSubring L) (u : Aˣ) (n : ℕ) :
    Chapter10ResidueField A →+ Chapter10ResidueField A where
  toFun a := ((chapter10UnitReduction A u) ^ n : Chapter10ResidueField A) * a
  map_zero' := by simp
  map_add' a b := by simp [mul_add]

/- The coordinate map itself depends on the chosen uniformizer; its existence
   is the noncanonical part of the layer identification. -/
noncomputable def chapter10UniformizerLayerCoordinate
    {L : Type*} [Field L] (A : ValuationSubring L) (π : A) (n : ℕ) :
    Multiplicative (Chapter10ResidueField A) →*
      Chapter10UnitLayerQuotient A n := by
  sorry

/-- A change `π ↦ uπ` rescales the `n`th coordinate by the residue of `uⁿ`. -/
theorem chapter10_uniformizer_change_rescales_layer
    {L : Type*} [Field L] (A : ValuationSubring L)
    (π π' : A) (u : Aˣ) (n : ℕ) (hn : 0 < n)
    (hπ : Chapter10Uniformizer A π)
    (hπ' : Chapter10Uniformizer A π')
    (hchange : π' = (u : A) * π) :
    ∀ a : Chapter10ResidueField A,
      chapter10UniformizerLayerCoordinate A π' n (Multiplicative.ofAdd a) =
        chapter10UniformizerLayerCoordinate A π n
          (Multiplicative.ofAdd (chapter10ResiduePowerScaling A u n a)) := by
  sorry

/-- The finite-precision unit quotient has valuation, residue, and additive-layer coordinates. -/
structure Chapter10UnitQuotientCoordinateProfile
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) where
  equivalence :
    Chapter10FieldUnitQuotient A n ≃*
        (Multiplicative ℤ ×
        ((Chapter10ResidueField A)ˣ ×
          (Fin (n - 1) → Multiplicative (Chapter10ResidueField A))))

/-- The coordinate profile asserted by the successive-layer decomposition. -/
theorem chapter10_unit_quotient_has_coordinates
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    [Fintype (Chapter10ResidueField A)]
    [Valuation.IsRankOneDiscrete A.valuation]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (π : A) (hπ : Chapter10Uniformizer A π) :
    Nonempty (Chapter10UnitQuotientCoordinateProfile A n) := by
  sorry

/-- The valuation-only quotient is the infinite cyclic magnitude coordinate. -/
theorem chapter10_field_unit_quotient_by_ring_units
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Valuation.IsRankOneDiscrete A.valuation]
    (π : A) (hπ : Chapter10Uniformizer A π) :
    Nonempty (Chapter10FieldUnitQuotient A 0 ≃* Multiplicative ℤ) := by
  sorry

/-- Finite residue fields give the index `(q-1)q^(n-1)` for `U⁰/Uⁿ`. -/
theorem chapter10_unit_quotient_cardinality
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n)
    [Fintype (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    Nat.card (Chapter10UnitRingQuotient A n) =
      (Fintype.card (Chapter10ResidueField A) - 1) *
        Fintype.card (Chapter10ResidueField A) ^ (n - 1) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
