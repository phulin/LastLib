import LastLib.Book05LocalClassFieldTheory.Chapter07.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- The canonical continuous multiplicative equivalence from the Galois group
of the chosen maximal abelian extension to its finite Galois inverse limit. -/
noncomputable def chapter07AbelianGaloisLimitEquiv
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    Gal(KAb / K) ≃ₜ*
      ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) :=
  LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01AbelianGaloisLimitEquiv K KAb

/-- Every finite Galois level of an abelian extension is itself abelian. -/
theorem chapter07_finite_level_is_abelian
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (L : Chapter07FiniteAbelianIndex K KAb) :
    IsAbelianGalois K L := by
  infer_instance

/-- The finite Artin map descended to the norm quotient. -/
noncomputable def chapter07FiniteReciprocityQuotientHom
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) →*
      Gal(L / K) :=
  QuotientGroup.lift
    (chapter07NormSubgroup (K := K) (L := L))
    (S.artin L) (by
      have hker : (S.artin L).ker =
          chapter07NormSubgroup (K := K) (L := L) := by
        simpa only [chapter07NormSubgroup] using S.kernel_eq_norm L
      exact le_of_eq hker.symm)

/-- The descended finite map composed with the quotient projection is the
finite Artin map itself. -/
theorem chapter07FiniteReciprocityQuotientHom_comp_mk
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    (chapter07FiniteReciprocityQuotientHom S L).comp
        (QuotientGroup.mk'
          (chapter07NormSubgroup (K := K) (L := L))) =
      S.artin L := by
  sorry

/-- The finite reciprocity equivalence obtained from the Artin map and its
norm kernel. -/
noncomputable def chapter07FiniteReciprocityEquiv
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
      Gal(L / K) := by
  let hker : (S.artin L).ker =
      chapter07NormSubgroup (K := K) (L := L) := by
    simpa only [chapter07NormSubgroup] using S.kernel_eq_norm L
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (S.artin L) (S.surjective L))

/-- The local reciprocity map obtained by applying the inverse-limit Galois
equivalence to the compatible tuple of finite Artin maps. -/
noncomputable def chapter07LocalReciprocity
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Kˣ →* Gal(KAb / K) :=
  (chapter07AbelianGaloisLimitEquiv K KAb).symm.toMulEquiv.toMonoidHom.comp
    S.toLimitHom

/-- The finite projection of the inverse-limit tuple is the prescribed finite
Artin map. -/
theorem chapter07_finite_artin_is_the_reciprocity_projection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) (x : Kˣ) :
    InfiniteGalois.proj L
        ((chapter07AbelianGaloisLimitEquiv K KAb)
          (chapter07LocalReciprocity S x)) =
      S.artin L x := by
  sorry

/-- Equivalent restriction formulation of the finite projection statement. -/
theorem chapter07_local_reciprocity_restricts_to_artin
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) (x : Kˣ) :
    AlgEquiv.restrictNormalHom L
        (chapter07LocalReciprocity S x) =
      S.artin L x := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the maximality property of the chosen K-ab model
is the cofinality bridge from arbitrary finite abelian extensions to the
canonical finite Galois-intermediate-field index. -/
theorem chapter07_finite_abelian_levels_are_cofinal
    {K : Type u} {KAb : Type v} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (hmax : chapter07IsMaximalAbelianExtension K KAb)
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ∃ M : Chapter07FiniteAbelianIndex K KAb, Nonempty (L ≃ₐ[K] M) := by
  sorry

/- The inverse-limit construction is indexed by the chosen canonical model,
but the source theorem quantifies over every finite abelian extension.  The
following bridge transports the canonical finite reciprocity equivalence
across the algebra equivalence supplied by cofinality. -/
theorem chapter07_finite_abelian_extension_reciprocity
    {K : Type u} {KAb : Type v} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (S : Chapter07FiniteArtinSystem K KAb)
    (hmax : chapter07IsMaximalAbelianExtension K KAb)
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Nonempty
      (Kˣ ⧸ chapter07NormSubgroup (K := K) (L := L) ≃*
        Gal(L / K)) := by
  sorry

/-- The inverse-limit equivalence in the source notation
Galois-abelian-group equals Gal of the maximal abelian extension. -/
noncomputable def chapter07_galois_ab_is_the_inverse_limit_equiv
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    Gal(KAb / K) ≃ₜ*
      ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) :=
  chapter07AbelianGaloisLimitEquiv K KAb

/-- The inverse-limit statement in proposition form. -/
theorem chapter07_galois_ab_is_the_inverse_limit
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    Nonempty
      (Gal(KAb / K) ≃ₜ*
        ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb)) :=
  ⟨chapter07_galois_ab_is_the_inverse_limit_equiv (K := K) (KAb := KAb)⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
