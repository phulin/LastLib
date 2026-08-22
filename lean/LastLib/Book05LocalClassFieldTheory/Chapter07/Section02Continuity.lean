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
  constructor
  · intro hf i
    exact (continuous_apply i).comp (continuous_subtype_val.comp hf)
  · intro hf
    apply continuous_induced_rng.mpr
    exact continuous_pi hf

/-- Continuity of local reciprocity is equivalent to continuity at every
finite Artin level. -/
theorem chapter07_local_reciprocity_continuous_iff_finite_artin
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Continuous (chapter07LocalReciprocity S) ↔
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Continuous (S.artin L) := by
  let e := chapter07AbelianGaloisLimitEquiv K KAb
  constructor
  · intro h L
    have hlim : Continuous (fun x : Kˣ => e (chapter07LocalReciprocity S x)) :=
      e.continuous.comp h
    have hcoords :=
      (chapter07_continuous_to_limit_iff
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb)
        (fun x : Kˣ => e (chapter07LocalReciprocity S x))).1 hlim
    have hcoord := hcoords (Opposite.op L)
    change @Continuous Kˣ (L ≃ₐ[K] L) _ (⊥ : TopologicalSpace (L ≃ₐ[K] L))
      (fun x : Kˣ => InfiniteGalois.proj L (e (chapter07LocalReciprocity S x))) at hcoord
    have hproj : Continuous (fun x : Kˣ =>
        InfiniteGalois.proj L (e (chapter07LocalReciprocity S x))) := by
      convert! hcoord
      exact DiscreteTopology.eq_bot (α := L ≃ₐ[K] L)
    convert hproj using 1
    funext x
    exact (chapter07_finite_artin_is_the_reciprocity_projection S L x).symm
  · intro h
    have hcoords : ∀ i : (FiniteGaloisIntermediateField K KAb)ᵒᵖ,
        Continuous (fun x : Kˣ =>
          (e (chapter07LocalReciprocity S x)).val i) := by
      intro i
      have hproj : Continuous (fun x : Kˣ =>
          InfiniteGalois.proj i.unop (e (chapter07LocalReciprocity S x))) := by
        convert h i.unop using 1
        funext x
        exact chapter07_finite_artin_is_the_reciprocity_projection S i.unop x
      change @Continuous Kˣ (i.unop ≃ₐ[K] i.unop) _
        (⊥ : TopologicalSpace (i.unop ≃ₐ[K] i.unop))
        (fun x : Kˣ => InfiniteGalois.proj i.unop (e (chapter07LocalReciprocity S x)))
      convert! hproj
      exact (DiscreteTopology.eq_bot (α := i.unop ≃ₐ[K] i.unop)).symm
    have hlim : Continuous (fun x : Kˣ => e (chapter07LocalReciprocity S x)) :=
      (chapter07_continuous_to_limit_iff
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb)
        (fun x : Kˣ => e (chapter07LocalReciprocity S x))).2 hcoords
    have hcomp : Continuous (fun x : Kˣ =>
        e.symm (e (chapter07LocalReciprocity S x))) :=
      e.symm.continuous.comp hlim
    convert hcomp using 1
    funext x
    exact (e.symm_apply_apply _).symm

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
  rw [chapter07_local_reciprocity_continuous_iff_finite_artin S]
  constructor
  · intro h L
    convert h L using 1
    funext x
    exact chapter07_finite_artin_is_the_reciprocity_projection S L x
  · intro h L
    convert h L using 1
    funext x
    exact (chapter07_finite_artin_is_the_reciprocity_projection S L x).symm

/-- For a finite discrete target, an abstract quotient homomorphism is
continuous as soon as its kernel is open. -/
theorem chapter07_finite_quotient_continuous_of_open_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hker : IsOpen (f.ker : Set G)) :
    Continuous f := by
  apply continuous_of_continuousAt_one f
  rw [continuousAt_def]
  intro U hU
  rw [f.map_one] at hU
  have hU1 : (1 : H) ∈ U := mem_nhds_discrete.mp hU
  refine Filter.mem_of_superset (hker.mem_nhds ?_) ?_
  · exact f.map_one
  · intro x hx
    change f x ∈ U
    change f x = 1 at hx
    rw [hx]
    exact hU1

/-- The finite quotient criterion in both directions. -/
theorem chapter07_finite_quotient_continuous_iff_open_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) :
    Continuous f ↔ IsOpen (f.ker : Set G) := by
  constructor
  · intro hf
    change IsOpen (f ⁻¹' ({1} : Set H))
    exact hf.isOpen_preimage _ (isOpen_discrete _)
  · exact chapter07_finite_quotient_continuous_of_open_kernel f

/-- A finite Artin map is continuous once its norm kernel is open. -/
theorem chapter07_finite_artin_continuous_of_open_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb)
    (hopen :
      IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    Continuous (S.artin L) := by
  apply chapter07_finite_quotient_continuous_of_open_kernel (S.artin L)
  rw [chapter07_finite_artin_kernel_eq_norm S L]
  exact hopen

/-- Continuity of local reciprocity from openness of every finite norm group. -/
theorem chapter07_local_reciprocity_continuous
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    Continuous (chapter07LocalReciprocity S) := by
  exact (chapter07_local_reciprocity_continuous_iff_finite_artin S).2
    (fun L => chapter07_finite_artin_continuous_of_open_norm S L (hopen L))

/-- The inverse image of the basic Galois neighborhood fixing a finite level
is exactly the corresponding norm subgroup. -/
theorem chapter07_reciprocity_preimage_fixing_subgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    (chapter07LocalReciprocity S) ⁻¹'
        (L.fixingSubgroup : Set Gal(KAb / K)) =
      (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ) := by
  ext x
  change chapter07LocalReciprocity S x ∈ (L.fixingSubgroup : Set Gal(KAb / K)) ↔
    x ∈ chapter07NormSubgroup (K := K) (L := L)
  have hfix :
      chapter07LocalReciprocity S x ∈ (L.fixingSubgroup : Set Gal(KAb / K)) ↔
        (chapter07LocalReciprocity S x).restrictNormalHom L = 1 := by
    simpa only [SetLike.mem_coe] using
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff
        (chapter07LocalReciprocity S x) L)
  rw [hfix]
  change InfiniteGalois.proj L
      ((chapter07AbelianGaloisLimitEquiv K KAb)
        (chapter07LocalReciprocity S x)) = 1 ↔
    x ∈ chapter07NormSubgroup (K := K) (L := L)
  rw [chapter07_finite_artin_is_the_reciprocity_projection S L x]
  change x ∈ (S.artin L).ker ↔ _
  rw [chapter07_finite_artin_kernel_eq_norm S L]

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
