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
    Continuous R.reciprocity ∧ Function.Injective R.reciprocity ∧
      Dense (Set.range R.reciprocity) := by
  sorry

/-- The profinite completion of the multiplicative group is the abelianized
Galois group. -/
theorem chapter12_profinite_completion_equiv_galois_abelianization
    {K G : Type*} [Field K] [CommGroup G]
    [TopologicalSpace Kˣ] [TopologicalSpace G]
    [IsTopologicalGroup Kˣ] [IsTopologicalGroup G]
    (_P : Chapter12LocalFieldProfile K)
    (R : Chapter12ReciprocityLimit K G)
    : Nonempty (Chapter12TopologicalGroupEquiv
      (LastLib.Book05LocalClassFieldTheory.Chapter11.Chapter11ProfiniteCompletion Kˣ)
      (TopologicalAbelianization G)) := by
  exact ⟨R.completionEquiv⟩

/-- The finite and infinite forms of the dictionary have the same kernel
language: finite kernels are norm subgroups, and the infinite map is obtained
by their compatible inverse-limit restrictions. -/
theorem chapter12_finite_kernels_are_norm_subgroups
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) :
    A.artin.reciprocity.ker = chapter12NormSubgroup K L := by
  exact chapter12_finite_artin_kernel_eq_norm K L A

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
