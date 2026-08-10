import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section07GaloisActionOnTheLayers

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

set_option maxHeartbeats 800000

open Ideal IsLocalRing

/-! ## 10.8. Completeness and inverse limits of units -/

/-- Reduction from precision `n+1` to precision `n`. -/
noncomputable def chapter10PrecisionRingTransition
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Chapter10PrecisionQuotient A (n + 1) →+*
      Chapter10PrecisionQuotient A n := by
  sorry

/-- The induced transition map on finite-precision unit groups. -/
def chapter10PrecisionUnitTransition
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    (Chapter10PrecisionQuotient A (n + 1))ˣ →*
      (Chapter10PrecisionQuotient A n)ˣ :=
  Units.map (chapter10PrecisionRingTransition A n).toMonoidHom

/-- An opaque name for a finite-precision unit group, avoiding quotient unfolding in families. -/
def Chapter10PrecisionUnitGroup
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) : Type _ :=
  (Chapter10PrecisionQuotient A (n + 1))ˣ

instance chapter10PrecisionUnitGroupGroup
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Group (Chapter10PrecisionUnitGroup A n) := by
  change Group ((Chapter10PrecisionQuotient A (n + 1))ˣ)
  infer_instance

/-- The abstract transition used by the inverse-limit interface. -/
noncomputable def chapter10AbstractPrecisionUnitTransition
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Chapter10PrecisionUnitGroup A (n + 1) →*
      Chapter10PrecisionUnitGroup A n := by
  change (Chapter10PrecisionQuotient A (n + 2))ˣ →*
    (Chapter10PrecisionQuotient A (n + 1))ˣ
  exact chapter10PrecisionUnitTransition A (n + 1)

/-- A compatible family of units in all finite congruence quotients. -/
def Chapter10CompatibleUnitFamily
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Subgroup (∀ n : ℕ, Chapter10PrecisionUnitGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrecisionUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrecisionUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrecisionUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit group of finite-precision units. -/
abbrev Chapter10AdicUnitInverseLimit
    {L : Type*} [Field L] (A : ValuationSubring L) : Type _ :=
  Chapter10CompatibleUnitFamily A

/-- The canonical compatible family attached to a ring unit. -/
noncomputable def chapter10UnitToAdicInverseLimit
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Aˣ →* Chapter10AdicUnitInverseLimit A := by
  sorry

/-- Completeness identifies ring units with the inverse limit of their reductions. -/
theorem chapter10_complete_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    Nonempty (Aˣ ≃* Chapter10AdicUnitInverseLimit A) := by
  sorry

/-- The finite-precision quotients of the principal-unit group. -/
abbrev Chapter10PrincipalUnitPrecisionQuotient
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) : Type _ :=
  chapter10UnitFiltration A 1 ⧸
    (chapter10UnitFiltration A (n + 1)).subgroupOf (chapter10UnitFiltration A 1)

/-- Reduction between successive principal-unit precision quotients. -/
noncomputable def chapter10PrincipalUnitTransition
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
      Chapter10PrincipalUnitPrecisionQuotient A n := by
  sorry

/-- An opaque name for a principal-unit precision quotient. -/
def Chapter10PrincipalUnitPrecisionGroup
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) : Type _ :=
  Chapter10PrincipalUnitPrecisionQuotient A n

instance chapter10PrincipalUnitPrecisionGroupGroup
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Group (Chapter10PrincipalUnitPrecisionGroup A n) := by
  change Group (Chapter10PrincipalUnitPrecisionQuotient A n)
  infer_instance

/-- The abstract transition used by the principal-unit inverse-limit interface. -/
noncomputable def chapter10AbstractPrincipalUnitTransition
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    Chapter10PrincipalUnitPrecisionGroup A (n + 1) →*
      Chapter10PrincipalUnitPrecisionGroup A n := by
  change Chapter10PrincipalUnitPrecisionQuotient A (n + 1) →*
    Chapter10PrincipalUnitPrecisionQuotient A n
  exact chapter10PrincipalUnitTransition A n

/-- A compatible family of principal units modulo every deeper subgroup. -/
def Chapter10CompatiblePrincipalUnitFamily
    {L : Type*} [Field L] (A : ValuationSubring L) :
    Subgroup (∀ n : ℕ, Chapter10PrincipalUnitPrecisionGroup A n) where
  carrier := {x | ∀ n,
    chapter10AbstractPrincipalUnitTransition A n (x (n + 1)) = x n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hxy hy n
    change chapter10AbstractPrincipalUnitTransition A n
        (x (n + 1) * y (n + 1)) = x n * y n
    rw [map_mul, hxy n, hy n]
  inv_mem' := by
    intro x hxy n
    change chapter10AbstractPrincipalUnitTransition A n
        ((x (n + 1))⁻¹) = (x n)⁻¹
    rw [map_inv, hxy n]

/-- The inverse-limit type for principal units. -/
abbrev Chapter10PrincipalUnitInverseLimit
    {L : Type*} [Field L] (A : ValuationSubring L) : Type _ :=
  Chapter10CompatiblePrincipalUnitFamily A

/-- Completeness identifies principal units with their compatible finite layers. -/
theorem chapter10_complete_principal_units_inverse_limit
    {L : Type*} [Field L] (A : ValuationSubring L)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A) :
    Nonempty
      (chapter10UnitFiltration A 1 ≃*
        Chapter10PrincipalUnitInverseLimit A) := by
  sorry

/-- Finite residue fields make every finite-precision quotient finite. -/
theorem chapter10_finite_residue_finite_precision_quotients
    {L : Type*} [Field L] (A : ValuationSubring L)
    [Finite (Chapter10ResidueField A)] (n : ℕ)
    (hDVR : IsDiscreteValuationRing A) :
    Finite (Chapter10PrecisionQuotient A (n + 1)) := by
  sorry

/-- Under the adic topology, finite residue fields make the unit group compact. -/
theorem chapter10_finite_residue_unit_group_compact
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    Chapter10CompactUnitGroup (G := Aˣ) := by
  sorry

/-- Each congruence subgroup is compact and open in the finite-residue case. -/
theorem chapter10_finite_residue_unit_filtration_compact_open
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] [Finite (Chapter10ResidueField A)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    ∀ n : ℕ,
      IsCompact (chapter10UnitFiltration A n : Set Aˣ) ∧
        IsOpen (chapter10UnitFiltration A n : Set Aˣ) := by
  sorry

/-- The valuation direction is discrete and is the only noncompact direction. -/
def Chapter10LocallyCompactButNotCompact
    (G : Type*) [TopologicalSpace G] : Prop :=
  LocallyCompactSpace G ∧ ¬ IsCompact (Set.univ : Set G)

/-- With finite residue field, a complete valued field is locally compact but not compact. -/
theorem chapter10_finite_residue_local_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Lˣ] [Finite (Chapter10ResidueField A)]
    [Valuation.IsRankOneDiscrete A.valuation]
    (π : A) (hπ : Chapter10Uniformizer A π)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hDVR : IsDiscreteValuationRing A)
    (htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10FieldUnitFiltration A)) :
    Chapter10LocallyCompactButNotCompact Lˣ := by
  sorry

/-- An infinite residue-unit quotient obstructs compactness of the unit group. -/
theorem chapter10_infinite_residue_prevents_unit_compactness
    {L : Type*} [Field L] (A : ValuationSubring L)
    [TopologicalSpace Aˣ] [TopologicalSpace (Chapter10ResidueField A)ˣ]
    [Infinite (Chapter10ResidueField A)]
    (hquotient_discrete :
      ∀ s : Set (Chapter10ResidueField A)ˣ,
        IsOpen s)
    (hresidue_surjective : Function.Surjective (chapter10UnitReduction A))
    (hresidue_continuous : Continuous (chapter10UnitReduction A)) :
    ¬ Chapter10CompactUnitGroup (G := Aˣ) := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
