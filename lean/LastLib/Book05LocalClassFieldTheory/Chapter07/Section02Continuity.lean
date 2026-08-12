import LastLib.Book05LocalClassFieldTheory.Chapter07.Section01PassageThroughFiniteQuotients

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-- The finite Artin kernel is the finite norm subgroup. -/
theorem chapter07_finite_artin_kernel_eq_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    (S.artin L).ker =
      chapter07NormSubgroup (K := K) (L := L) :=
  S.kernel_eq_norm L

/-- Openness of a finite Artin kernel follows from openness of its norm group. -/
theorem chapter07_finite_artin_kernel_is_open
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hopen :
      IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    IsOpen ((S.artin L).ker : Set Kˣ) := by
  rw [chapter07_finite_artin_kernel_eq_norm S L]
  exact hopen

/-- A map into a profinite inverse limit is continuous exactly when all
finite-coordinate maps are continuous. -/
theorem chapter07_continuous_to_limit_iff
    {I : Type*} [Category I] (F : I ⥤ ProfiniteGrp)
    {X : Type*} [TopologicalSpace X]
    (f : X → ProfiniteGrp.limit F) :
    Continuous f ↔
      ∀ i : I, Continuous (fun x => (f x).val i) := by
  sorry

/-- Continuity of local reciprocity is equivalent to continuity at every
finite Artin level. -/
theorem chapter07_local_reciprocity_continuous_iff_finite_artin
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Continuous (chapter07LocalReciprocity S) ↔
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Continuous (S.artin L) := by
  sorry

/-- The same continuity criterion written with the canonical finite
projections of the Galois inverse limit. -/
theorem chapter07_local_reciprocity_continuous_iff_finite_projections
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Continuous (chapter07LocalReciprocity S) ↔
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Continuous (fun x : Kˣ =>
          InfiniteGalois.proj L
            ((chapter07AbelianGaloisLimitEquiv K KAb)
              (chapter07LocalReciprocity S x))) := by
  sorry

/-- For a finite discrete target, an abstract quotient homomorphism is
continuous as soon as its kernel is open. -/
theorem chapter07_finite_quotient_continuous_of_open_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hker : IsOpen (f.ker : Set G)) :
    Continuous f := by
  sorry

/-- The finite quotient criterion in both directions. -/
theorem chapter07_finite_quotient_continuous_iff_open_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) :
    Continuous f ↔ IsOpen (f.ker : Set G) := by
  sorry

/-- A finite Artin map is continuous once its norm kernel is open. -/
theorem chapter07_finite_artin_continuous_of_open_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hopen :
      IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    Continuous (S.artin L) := by
  sorry

/-- Continuity of local reciprocity from openness of every finite norm group. -/
theorem chapter07_local_reciprocity_continuous
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    Continuous (chapter07LocalReciprocity S) := by
  sorry

/-- The inverse image of the basic Galois neighborhood fixing a finite level
is exactly the corresponding norm subgroup. -/
theorem chapter07_reciprocity_preimage_fixing_subgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    (chapter07LocalReciprocity S) ⁻¹'
        (L.fixingSubgroup : Set Gal(KAb / K)) =
      (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ) := by
  sorry

/-- The neighborhood version of continuity: norm subgroups pull back the
finite-level fixing neighborhoods. -/
theorem chapter07_reciprocity_norm_neighborhood
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hopen :
      IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    IsOpen ((chapter07LocalReciprocity S) ⁻¹'
      (L.fixingSubgroup : Set Gal(KAb / K))) := by
  rw [chapter07_reciprocity_preimage_fixing_subgroup S L]
  exact hopen

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
