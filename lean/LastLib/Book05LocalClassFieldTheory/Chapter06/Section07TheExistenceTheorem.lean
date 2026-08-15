import LastLib.Book05LocalClassFieldTheory.Chapter06.Section06AddingTheUnramifiedDirection

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators

/-!
### 6.7. The existence theorem
-/

/- The source constructs the desired field as a fixed field in a finite
   precision extension.  This record keeps the quotient map and the fixed
   field operation visible at the API boundary. -/

noncomputable def chapter06FixedFieldOfArtinImage
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ) :
    IntermediateField K L :=
  IntermediateField.fixedField (Subgroup.map A.reciprocity H)

theorem chapter06_mem_fixedFieldOfArtinImage_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ) (x : L) :
    x ∈ chapter06FixedFieldOfArtinImage A H ↔
      ∀ σ ∈ Subgroup.map A.reciprocity H, σ x = x := by
  sorry

theorem chapter06_finite_reciprocity_quotient_exists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) :
    Nonempty ((Kˣ ⧸ A.reciprocity.ker) ≃* Gal(L / K)) := by
  sorry

theorem chapter06_finite_reciprocity_norm_quotient_exists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) :
    Nonempty ((Kˣ ⧸ chapter06NormSubgroup K L) ≃* Gal(L / K)) := by
  sorry

theorem chapter06_fixedFieldOfArtinImage_finite_abelian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ)
    [FiniteDimensional K (chapter06FixedFieldOfArtinImage A H)] :
    IsGalois K (chapter06FixedFieldOfArtinImage A H) ∧
      ∀ σ τ : Gal(chapter06FixedFieldOfArtinImage A H / K),
        σ * τ = τ * σ := by
  sorry

theorem chapter06_fixedFieldOfArtinImage_norm_group
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ)
    (hkernel : A.reciprocity.ker ≤ H)
    [FiniteDimensional K (chapter06FixedFieldOfArtinImage A H)] :
    chapter06NormSubgroup K (chapter06FixedFieldOfArtinImage A H) = H := by
  sorry

theorem chapter06_fixedFieldOfArtinImage_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ)
    (hkernel : A.reciprocity.ker ≤ H)
    [FiniteDimensional K (chapter06FixedFieldOfArtinImage A H)] :
    Module.finrank K (chapter06FixedFieldOfArtinImage A H) =
      Nat.card (Kˣ ⧸ H) := by
  sorry

/-- The finite-precision realization supplied conditionally by Hypothesis NF
and the torsion/unramified compositum calculation in §6.6. -/
def Chapter06PrecisionNormInput
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    ∃ L : Chapter06FiniteAbelianSubextension K KAb,
      L.normSubgroup = chapter06PrecisionSubgroup D m n

/-- Precision subgroups are realized only after the NF input is supplied. -/
theorem chapter06_precision_subgroup_is_realized
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ L : Chapter06FiniteAbelianSubextension K KAb,
      L.normSubgroup = chapter06PrecisionSubgroup D m n := by
  exact hNF m n hm hn

theorem chapter06_open_finite_index_contains_realizable_precision
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    ∃ L : Chapter06FiniteAbelianSubextension K KAb,
      L.normSubgroup ≤ H := by
  sorry

theorem chapter06FiniteAbelianSubextension_ext
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L₁ L₂ : Chapter06FiniteAbelianSubextension K KAb)
    (hfield : L₁.field = L₂.field) : L₁ = L₂ := by
  sorry

theorem chapter06_finite_artin_map_exists_for_subextension
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L : Chapter06FiniteAbelianSubextension K KAb) :
    letI : FiniteDimensional K L.field := L.finite
    letI : IsGalois K L.field := L.galois
    letI : Fintype (Gal(L.field / K)) := L.galois_group_finite
    Nonempty
      (@Chapter06FiniteArtinMap K L.field _ _ _ L.finite L.galois
        L.galois_group_finite
        (chapter06FiniteAbelianSubextension.isAbelian L)) := by
  sorry

/-- The fixed-field step in the source proof, with the finite quotient made
explicit as a hypothesis rather than hidden in prose. -/
theorem chapter06_fixed_field_step
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) (H : Subgroup Kˣ)
    (hkernel : A.reciprocity.ker ≤ H)
    [FiniteDimensional K (chapter06FixedFieldOfArtinImage A H)] :
    chapter06NormSubgroup K (chapter06FixedFieldOfArtinImage A H) = H ∧
      Module.finrank K (chapter06FixedFieldOfArtinImage A H) =
        Nat.card (Kˣ ⧸ H) := by
  exact ⟨chapter06_fixedFieldOfArtinImage_norm_group A H hkernel,
    chapter06_fixedFieldOfArtinImage_degree A H hkernel⟩

theorem chapter06_local_existence_exists
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    ∃ L : Chapter06FiniteAbelianSubextension K KAb,
      L.normSubgroup = H ∧
        L.degree = Nat.card (Kˣ ⧸ H) := by
  sorry

theorem chapter06_local_existence_unique
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex)
    (L₁ L₂ : Chapter06FiniteAbelianSubextension K KAb)
    (h₁ : L₁.normSubgroup = H) (h₂ : L₂.normSubgroup = H) :
    L₁ = L₂ := by
  sorry

/-- The source-facing local existence theorem, conditional on Hypothesis NF. -/
theorem chapter06_local_existence_theorem
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    ∃! L : Chapter06FiniteAbelianSubextension K KAb,
      L.normSubgroup = H ∧
        L.degree = Nat.card (Kˣ ⧸ H) := by
  sorry

/-- A chosen field supplied by the existence theorem. -/
noncomputable def chapter06ExtensionOfOpenSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    Chapter06FiniteAbelianSubextension K KAb :=
  Classical.choose
    (chapter06_local_existence_exists D hmax hNF htop H hopen hfinite)

theorem chapter06ExtensionOfOpenSubgroup_normSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    (chapter06ExtensionOfOpenSubgroup D hmax hNF htop H hopen hfinite).normSubgroup = H := by
  exact (Classical.choose_spec
    (chapter06_local_existence_exists D hmax hNF htop H hopen hfinite)).1

theorem chapter06ExtensionOfOpenSubgroup_degree
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    (chapter06ExtensionOfOpenSubgroup D hmax hNF htop H hopen hfinite).degree =
      Nat.card (Kˣ ⧸ H) := by
  exact (Classical.choose_spec
    (chapter06_local_existence_exists D hmax hNF htop H hopen hfinite)).2

theorem chapter06_local_existence_degree
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex)
    (L : Chapter06FiniteAbelianSubextension K KAb)
    (hL : L.normSubgroup = H) :
    L.degree = Nat.card (Kˣ ⧸ H) := by
  sorry

theorem chapter06_local_existence_uniqueness_of_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (D : Chapter06LocalFieldData K)
    (hmax : Chapter06IsMaximalAbelianExtension K KAb)
    (hNF : Chapter06PrecisionNormInput (KAb := KAb) D)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex)
    (L : Chapter06FiniteAbelianSubextension K KAb)
    (hL : L.normSubgroup = H) :
    L = chapter06ExtensionOfOpenSubgroup D hmax hNF htop H hopen hfinite := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
