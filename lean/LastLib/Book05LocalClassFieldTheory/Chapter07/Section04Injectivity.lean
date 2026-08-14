import LastLib.Book05LocalClassFieldTheory.Chapter07.Section03DensityAndSurjectivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite
open scoped BigOperators

/-- The kernel of the infinite map is the intersection of all finite norm
subgroups. -/
theorem chapter07_local_reciprocity_kernel_eq_norm_intersection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    (chapter07LocalReciprocity S).ker =
      ⨅ L : Chapter07FiniteAbelianIndex K KAb,
        chapter07NormSubgroup (K := K) (L := L) := by
  sorry

/-- Membership in the kernel is forced into every explicit finite-precision
subgroup supplied by the local existence construction. -/
theorem chapter07_local_reciprocity_kernel_le_precision
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    (chapter07LocalReciprocity S).ker ≤
      chapter07PrecisionIntersection D := by
  sorry

/-- The intersection of all positive precision subgroups is trivial. -/
theorem chapter07_precision_intersection_eq_bot
    {G : Type*} [CommGroup G] (D : Chapter07PrecisionData G) :
    chapter07PrecisionIntersection D = ⊥ := by
  sorry

/-- The infinite reciprocity map has trivial kernel once the cofinal
precision family is available. -/
theorem chapter07_local_reciprocity_kernel_eq_bot
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    (chapter07LocalReciprocity S).ker = ⊥ := by
  apply le_antisymm
  · exact
      (chapter07_local_reciprocity_kernel_le_precision S D hcofinal).trans
        (le_of_eq (chapter07_precision_intersection_eq_bot D))
  · exact bot_le

/-- Injectivity is the kernel form of the infinite reciprocity statement. -/
theorem chapter07_local_reciprocity_injective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    Function.Injective (chapter07LocalReciprocity S) := by
  sorry

/-- The finite quotient form retained in Theorem 7.2. -/
theorem chapter07_local_reciprocity_finite_quotient
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Nonempty
      (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
        Gal(L / K)) :=
  ⟨chapter07FiniteReciprocityEquiv S L⟩

/-- The exact infinite local reciprocity theorem: continuous, injective,
dense, and an isomorphism on every finite abelian quotient. -/
theorem chapter07_local_reciprocity_theorem
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (D : Chapter07PrecisionData Kˣ)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hcofinal : chapter07KernelCofinality (KAb := KAb) D) :
    Continuous (chapter07LocalReciprocity S) ∧
      Function.Injective (chapter07LocalReciprocity S) ∧
      DenseRange (chapter07LocalReciprocity S) ∧
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Nonempty
          (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
            Gal(L / K)) := by
  refine ⟨chapter07_local_reciprocity_continuous S hopen, ?_, ?_, ?_⟩
  · exact chapter07_local_reciprocity_injective S D hcofinal
  · exact chapter07_local_reciprocity_dense S
  · intro L
    exact chapter07_local_reciprocity_finite_quotient S L

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
