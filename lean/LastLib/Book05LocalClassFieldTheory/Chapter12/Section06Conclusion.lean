import LastLib.Book05LocalClassFieldTheory.Chapter12.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.6. Conclusion -/

/-- The infinite reciprocity map is a continuous injective homomorphism with
dense image. -/
theorem chapter12_reciprocity_is_continuous_injective_dense
    {K G : Type*} [Field K] [CommGroup G]
    [TopologicalSpace Kˣ] [TopologicalSpace G]
    [IsTopologicalGroup Kˣ] [IsTopologicalGroup G]
    (_P : Chapter12LocalFieldProfile K)
    (R : Chapter12ReciprocityLimit K G) :
    Continuous R.map ∧ Function.Injective R.map ∧
      Dense (Set.range R.map) := by
  exact ⟨R.continuous_map, R.injective_map, R.dense_range_map⟩

/-- The profinite completion of the multiplicative group is the abelianized
Galois group. -/
-- DEPENDENCY_GUESS: The inverse-limit comparison is the final assembly of
-- the finite reciprocity and existence theorems from missing Book 5 chapters.
theorem chapter12_profinite_completion_equiv_galois_abelianization
    {K G Khat : Type*} [Field K] [CommGroup G] [CommGroup Khat]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace Khat]
    [IsTopologicalGroup Kˣ] [IsTopologicalGroup G] [IsTopologicalGroup Khat]
    (P : Chapter12LocalFieldProfile K)
    (R : Chapter12ReciprocityLimit K G)
    (C : Chapter12CompletionData Kˣ Khat) :
    Nonempty (Chapter12TopologicalGroupEquiv Khat G) := by
  sorry

/-- The finite and infinite forms of the dictionary have the same kernel
language: finite kernels are norm subgroups, and the infinite map is obtained
by their compatible inverse-limit restrictions. -/
theorem chapter12_finite_kernels_are_norm_subgroups
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter12FiniteAbelianExtension K L]
    (A : Chapter12FiniteArtinMap K L) :
    A.reciprocity.ker = chapter12NormSubgroup K L := by
  exact chapter12_finite_artin_kernel_eq_norm K L A

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
