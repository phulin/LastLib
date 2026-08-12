import LastLib.Book06GlobalClassFieldTheory.Chapter12.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter12

noncomputable section

open scoped Pointwise
open LastLib.Book06GlobalClassFieldTheory.Chapter06
open LastLib.Book06GlobalClassFieldTheory.Chapter10

/-! ## 12.1. Fields, subgroups, and quotients -/

theorem chapter12_canonical_field_subgroup_assignments_are_inverse
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A) :
    (∀ H : Chapter06OpenFiniteIndexSubgroup C,
        chapter06NormSubgroupOfExtension (G.extensionOfOpen H) = H.subgroup) ∧
      (∀ E : Chapter06FiniteAbelianExtension K Ks C,
        (G.extensionOfOpen (G.normSubgroupOfExtension E)).field = E.field) := by
  exact ⟨fun H => chapter06_global_existence_left_inverse A G H,
    fun E => chapter06_global_existence_right_inverse A G E⟩

theorem chapter12_canonical_open_subgroup_quotient_dictionary
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H : Chapter06OpenFiniteIndexSubgroup C) :
    Nonempty ((C ⧸ H.subgroup) ≃*
      Gal((G.extensionOfOpen H).field / K)) ∧
      Function.Surjective (G.artin H) ∧
      (G.artin H).ker = H.subgroup ∧
      Nat.card (C ⧸ H.subgroup) =
        chapter06GaloisDegree (K := K) (L := (G.extensionOfOpen H).field) := by
  exact ⟨⟨G.quotient_galois H⟩, G.artin_surjective H, G.artin_kernel H,
    G.quotient_index_degree H⟩

theorem chapter12_canonical_inclusion_reversal
    {K Ks C : Type*} [Field K] [Field Ks] [Algebra K Ks]
    [CommGroup C] [TopologicalSpace C]
    (A : Chapter06CharacterFieldAssignment K Ks C)
    (G : Chapter06GlobalExistenceCorrespondence K Ks C A)
    (H₁ H₂ : Chapter06OpenFiniteIndexSubgroup C) :
    H₁.subgroup ≤ H₂.subgroup ↔
      (G.extensionOfOpen H₂).field ≤ (G.extensionOfOpen H₁).field := by
  exact chapter06_global_existence_inclusion_reversal A G H₁ H₂

theorem chapter12_finite_abelian_norm_subgroup_is_open_and_finite_index
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    IsOpen (D.normSubgroup : Set C) ∧ D.normSubgroup.FiniteIndex := by
  exact ⟨D.normSubgroup_open, D.normSubgroup_finiteIndex⟩

def chapter12FiniteAbelianQuotientMap
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    C →* C ⧸ D.normSubgroup :=
  QuotientGroup.mk' D.normSubgroup

theorem chapter12_finite_abelian_quotient_galois_equiv
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    D.quotient_galois.toMonoidHom.comp
        (chapter12FiniteAbelianQuotientMap D) = D.artin := by
  exact D.quotient_artin

theorem chapter12_finite_abelian_degree_is_norm_index
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    Nat.card (C ⧸ D.normSubgroup) = Module.finrank K L := by
  exact D.quotient_index_degree

theorem chapter12_finite_abelian_degree_is_subgroup_index
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (D : Chapter12FiniteAbelianLevel K L C) :
    D.normSubgroup.index = Module.finrank K L := by
  rw [Subgroup.index_eq_card]
  exact D.quotient_index_degree

theorem chapter12_field_inclusion_iff_norm_subgroup_reverse
    {E C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12FieldSubgroupLattice E C)
    (A B : E) :
    D.fieldLe A B ↔ D.normSubgroup B ≤ D.normSubgroup A := by
  exact D.fieldLe_iff_norm_reverse A B

theorem chapter12_compositum_is_norm_subgroup_intersection
    {E C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12FieldSubgroupLattice E C)
    (A B : E) :
    D.normSubgroup (D.compositum A B) =
      D.normSubgroup A ⊓ D.normSubgroup B := by
  exact D.compositum_norm_intersection A B

theorem chapter12_field_intersection_is_norm_subgroup_product
    {E C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12FieldSubgroupLattice E C)
    (A B : E) :
    D.normSubgroup (D.intersection A B) =
      (D.normSubgroup A : Set C) * (D.normSubgroup B : Set C) := by
  exact D.intersection_norm_product A B

theorem chapter12_infinite_field_intersection_uses_closed_product
    {E C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] (D : Chapter12FieldSubgroupLattice E C)
    (I : Chapter12InfiniteFieldSubgroupData E C D) :
    D.normSubgroup I.fieldIntersection =
      chapter12ClosedProductSubgroup (D.normSubgroup '' I.fields) := by
  exact I.normSubgroup_intersection

theorem chapter12_nonabelian_norm_limitation
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup C] (D : Chapter12NonabelianLevel K L C) :
    D.normSubgroupL = D.normSubgroupM := by
  exact D.class_norm_limitation

theorem chapter12_nonabelian_class_norm_index_is_abelianization_order
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype (Gal(L / K))]
    [CommGroup C] (D : Chapter12NonabelianLevel K L C) :
    D.normSubgroupL.index = Nat.card (Abelianization (Gal(L / K))) := by
  exact D.class_norm_index

theorem chapter12_reciprocity_source_is_abelian
    {C : Type*} [CommGroup C] :
    ∀ x y : C, x * y = y * x := by
  intro x y
  exact mul_comm x y

/- The last row of the source table is the connected-component form of the
infinite theorem. -/
noncomputable def chapter12_abelianized_infinite_reciprocity
    {C K Kab : Type u} [CommGroup C] [TopologicalSpace C] [T2Space C]
    [IsTopologicalGroup C] [Field K] [Field Kab] [Algebra K Kab]
    [IsGalois K Kab]
    (T : Chapter10IdeleClassTopologyData C)
    (F : Chapter10FiniteArtinFamily C K Kab)
    (R : Chapter10FiniteReciprocityData F) :
    chapter10IdeleClassComponentQuotient C ≃ₜ* Gal(Kab / K) := by
  exact chapter10GlobalArtinQuotientEquiv T F R

end

end LastLib.Book06GlobalClassFieldTheory.Chapter12
