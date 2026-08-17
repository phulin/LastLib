import Mathlib.Data.ZMod.Basic
import LastLib.Book05LocalClassFieldTheory.Chapter06.Section01WhyASeparateExistenceConstructionIsNecessary
import LastLib.Book05LocalClassFieldTheory.Chapter06.Section05NormGroupOfTheTorsionExtension

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators

/-!
### 6.6. Adding the unramified direction
-/

/- The algebraic closure is used only as a common ambient field for the
   independently constructed finite levels.  The carrier-based record in
   `Dependencies` remains useful when an extension has already been given in
   an abstract presentation. -/

/-- A chosen unramified level inside the fixed algebraic closure. -/
structure Chapter06UnramifiedSubextension
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ) where
  field : IntermediateField K (AlgebraicClosure K)
  [finite : FiniteDimensional K field]
  [galois : IsGalois K field]
  [galois_group_finite : Fintype (Gal(field / K))]
  valued : Chapter06ValuedFiniteExtension D field
  degree_eq : Module.finrank K field = m
  unramified : Chapter06UnramifiedValuedExtension D valued

/-- The earlier local-field chapters supply the finite unramified-level
    construction represented by this chosen-subextension interface. -/
theorem chapter06_unramified_subextension_exists
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (hm : 0 < m) :
    Nonempty (Chapter06UnramifiedSubextension D m) := by
  sorry

theorem chapter06_unramified_subextension_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (U : Chapter06UnramifiedSubextension D m) :
    Module.finrank K U.field = m := by
  exact U.degree_eq

theorem chapter06_unramified_galois_group_card
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (U : Chapter06UnramifiedSubextension D m) :
    Nat.card (Gal(U.field / K)) = m := by
  sorry

theorem chapter06_unramified_galois_group_cyclic
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (U : Chapter06UnramifiedSubextension D m) :
    IsCyclic (Gal(U.field / K)) := by
  sorry

noncomputable def chapter06_unramified_frobenius_data
    {K : Type} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (U : Chapter06UnramifiedSubextension D m) :
    letI : FiniteDimensional K U.field := U.finite
    letI : IsGalois K U.field := U.galois
    letI : Fintype (Gal(U.field / K)) := U.galois_group_finite
    LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05UnramifiedExtensionData
      K U.field := by
  sorry

/-- The norm subgroup of an unramified level is
`π^(mℤ) U⁰ = π^(mℤ) 𝒪ˣ`. -/
theorem chapter06_unramified_norm_group
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) :
    chapter06UnramifiedNormSubgroup D m E =
      Subgroup.zpowers ((chapter06UniformizerUnit D) ^ m) ⊔
      Chapter06UnitFiltration D 0 := by
  sorry

theorem chapter06_unramified_norm_group_source_form
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) :
    chapter06UnramifiedNormSubgroup D m E =
      Subgroup.zpowers ((chapter06UniformizerUnit D) ^ m) ⊔
        chapter06ValuationRingUnitSubgroup D := by
  rw [chapter06_unramified_norm_group D m E,
    chapter06_unit_filtration_zero_eq_valuationRingUnits D]

theorem chapter06_unramified_norm_group_eq_precision
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) :
    chapter06UnramifiedNormSubgroup D m E =
      chapter06PrecisionSubgroup D m 0 := by
  exact chapter06_unramified_norm_group D m E

theorem chapter06_unramified_subextension_norm_group
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (U : Chapter06UnramifiedSubextension D m) :
    @chapter06NormSubgroup K U.field _ _ _ U.finite =
      chapter06PrecisionSubgroup D m 0 := by
  sorry

theorem chapter06_unramified_norm_mem_iff
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) (x : Kˣ) :
    x ∈ chapter06UnramifiedNormSubgroup D m E ↔
      ∃ z : ℤ, ∃ u : Kˣ,
        u ∈ Chapter06UnitFiltration D 0 ∧
          x = (chapter06UniformizerUnit D) ^ (m * z) * u := by
  sorry

theorem chapter06_unramified_norm_index
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (hm : 0 < m) (E : Chapter06UnramifiedExtension D m) :
    Nat.card (Kˣ ⧸ chapter06UnramifiedNormSubgroup D m E) = m := by
  sorry

/-- The source's trivial-intersection statement, expressed for intermediate
fields in the common algebraic closure. -/
theorem chapter06_torsion_unramified_trivial_intersection
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    (V : Chapter06ValuedFiniteExtension D
      (chapter06TorsionField D n ω.point))
    (hV : chapter06TotallyRamifiedValuedExtension D V)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m) :
    chapter06TorsionField D n ω.point ⊓ U.field = ⊥ := by
  sorry

/-- The compositum of the explicitly chosen torsion and unramified fields. -/
noncomputable def chapter06TorsionUnramifiedCompositum
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (_hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K
    ((chapter06TorsionField D n ω.point : Set (AlgebraicClosure K)) ∪
      (U.field : Set (AlgebraicClosure K)))

theorem chapter06_torsion_le_compositum
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m) :
    chapter06TorsionField D n ω.point ≤
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U := by
  sorry

theorem chapter06_unramified_le_compositum
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m) :
    U.field ≤ chapter06TorsionUnramifiedCompositum D n hn ω m hm U := by
  sorry

theorem chapter06_torsion_unramified_compositum_generated
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m) :
    IntermediateField.adjoin K
        ((chapter06TorsionField D n ω.point : Set (AlgebraicClosure K)) ∪
          (U.field : Set (AlgebraicClosure K))) =
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U := by
  rfl

/-- Finite reciprocity gives the norm subgroup of a compositum as an
intersection.  This generic form is reusable for the specialized precision
calculation below. -/
theorem chapter06_compositum_norm_group
    {K L₁ L₂ E : Type*} [Field K] [Field L₁] [Field L₂] [Field E]
    [Algebra K L₁] [Algebra K L₂] [Algebra K E]
    [Algebra L₁ E] [Algebra L₂ E]
    [IsScalarTower K L₁ E] [IsScalarTower K L₂ E]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K E]
    [IsGalois K L₁] [IsGalois K L₂] [IsGalois K E]
    [Fintype (Gal(L₁ / K))] [Fintype (Gal(L₂ / K))]
    [Fintype (Gal(E / K))]
    [Chapter06FiniteAbelianExtension K L₁]
    [Chapter06FiniteAbelianExtension K L₂]
    [Chapter06FiniteAbelianExtension K E]
    (C : Chapter06CompositumData K L₁ L₂ E) :
    chapter06NormSubgroup K E =
      chapter06NormSubgroup K L₁ ⊓ chapter06NormSubgroup K L₂ := by
  sorry

theorem chapter06_torsion_unramified_compositum_norm_group
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [Chapter06FiniteAbelianExtension K (chapter06TorsionField D n ω.point)]
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m)
    [FiniteDimensional K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [IsGalois K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [Fintype (Gal(
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U / K))]
    [Chapter06FiniteAbelianExtension K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)] :
    chapter06NormSubgroup K
        (chapter06TorsionUnramifiedCompositum D n hn ω m hm U) =
      chapter06PrecisionSubgroup D m n := by
  sorry

theorem chapter06_torsion_unramified_galois_product
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m)
    [FiniteDimensional K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [IsGalois K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [Fintype (Gal(
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U / K))]
    [CommGroup (Gal(
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U / K))] :
    Nonempty
      (Gal(chapter06TorsionUnramifiedCompositum D n hn ω m hm U / K) ≃*
        (Multiplicative (ZMod m)) ×
          (Chapter06TorsionResidueRing D n)ˣ) := by
  sorry

theorem chapter06_torsion_unramified_compositum_degree
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m)
    [FiniteDimensional K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)] :
    Module.finrank K
        (chapter06TorsionUnramifiedCompositum D n hn ω m hm U) =
      m * (chapter06ResidueCardinality D ^ (n - 1) *
        (chapter06ResidueCardinality D - 1)) := by
  sorry

theorem chapter06_precision_subgroups_are_compositum_norms
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (n : ℕ) (hn : 0 < n)
    (ω : Chapter06PrimitiveTorsionPoint D n hn)
    [FiniteDimensional K (chapter06TorsionField D n ω.point)]
    [IsGalois K (chapter06TorsionField D n ω.point)]
    [Fintype (Gal(chapter06TorsionField D n ω.point / K))]
    [Chapter06FiniteAbelianExtension K (chapter06TorsionField D n ω.point)]
    (m : ℕ) (hm : 0 < m)
    (U : Chapter06UnramifiedSubextension D m)
    [FiniteDimensional K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [IsGalois K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)]
    [Fintype (Gal(
      chapter06TorsionUnramifiedCompositum D n hn ω m hm U / K))]
    [Chapter06FiniteAbelianExtension K
      (chapter06TorsionUnramifiedCompositum D n hn ω m hm U)] :
    chapter06NormSubgroup K
        (chapter06TorsionUnramifiedCompositum D n hn ω m hm U) =
      chapter06PrecisionSubgroup D m n := by
  exact chapter06_torsion_unramified_compositum_norm_group
    D n hn ω m hm U

theorem chapter06_precision_family_is_neighborhood_basis
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D) :
    ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        chapter06PrecisionSubgroup D m n ≤ H := by
  exact chapter06_open_finite_index_contains_precision D htop

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
