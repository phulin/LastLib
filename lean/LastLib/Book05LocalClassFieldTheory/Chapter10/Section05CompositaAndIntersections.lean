import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

/-! ## 10.5. Composita and intersections -/

/- In the abelian multiplicative group, the product of two subgroups is their
   lattice supremum. -/
def chapter10NormSubgroupProduct
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) : Subgroup Kˣ :=
  H₁ ⊔ H₂

theorem chapter10_mem_normSubgroupProduct_iff
    {K : Type*} [Field K] (H₁ H₂ : Subgroup Kˣ) (x : Kˣ) :
    x ∈ chapter10NormSubgroupProduct H₁ H₂ ↔
      ∃ a ∈ H₁, ∃ b ∈ H₂, a * b = x := by
  sorry

theorem chapter10_compositum_norm_subgroup_eq_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K ↥(L₁ ⊔ L₂)] [FiniteDimensional K ↥(L₁ ⊓ L₂)] :
    chapter10NormSubgroup K (↥(L₁ ⊔ L₂)) =
      chapter10NormSubgroup K L₁ ⊓ chapter10NormSubgroup K L₂ := by
  sorry

theorem chapter10_intersection_norm_subgroup_eq_product
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K ↥(L₁ ⊔ L₂)] [FiniteDimensional K ↥(L₁ ⊓ L₂)] :
    chapter10NormSubgroup K (↥(L₁ ⊓ L₂)) =
      chapter10NormSubgroupProduct
        (chapter10NormSubgroup K L₁) (chapter10NormSubgroup K L₂) := by
  sorry

theorem chapter10_norm_subgroup_product_is_open_closed
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (H₁ H₂ : Subgroup Kˣ)
    (h₁open : IsOpen (H₁ : Set Kˣ))
    (h₂open : IsOpen (H₂ : Set Kˣ)) :
    IsOpen (chapter10NormSubgroupProduct H₁ H₂ : Set Kˣ) ∧
      IsClosed (chapter10NormSubgroupProduct H₁ H₂ : Set Kˣ) := by
  sorry

/- The formulas reverse field operations and subgroup operations. -/
theorem chapter10_compositum_intersection_reversal
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K ↥(L₁ ⊔ L₂)] [FiniteDimensional K ↥(L₁ ⊓ L₂)] :
    chapter10NormSubgroup K (↥(L₁ ⊔ L₂)) =
        chapter10NormSubgroup K L₁ ⊓ chapter10NormSubgroup K L₂ ∧
      chapter10NormSubgroup K (↥(L₁ ⊓ L₂)) =
        chapter10NormSubgroupProduct
          (chapter10NormSubgroup K L₁) (chapter10NormSubgroup K L₂) := by
  exact ⟨chapter10_compositum_norm_subgroup_eq_intersection L₁ L₂,
    chapter10_intersection_norm_subgroup_eq_product L₁ L₂⟩

theorem chapter10_compositum_degree_eq_norm_index
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K ↥(L₁ ⊔ L₂)] [FiniteDimensional K ↥(L₁ ⊓ L₂)] :
    Module.finrank K ↥(L₁ ⊔ L₂) =
      Nat.card
        (Kˣ ⧸
          (chapter10NormSubgroup K L₁ ⊓ chapter10NormSubgroup K L₂)) := by
  sorry

theorem chapter10_intersection_degree_eq_norm_index
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K ↥(L₁ ⊔ L₂)] [FiniteDimensional K ↥(L₁ ⊓ L₂)] :
    Module.finrank K ↥(L₁ ⊓ L₂) =
      Nat.card
        (Kˣ ⧸
          chapter10NormSubgroupProduct
            (chapter10NormSubgroup K L₁) (chapter10NormSubgroup K L₂)) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
