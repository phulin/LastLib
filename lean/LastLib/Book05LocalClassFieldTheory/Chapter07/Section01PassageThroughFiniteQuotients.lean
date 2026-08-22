import LastLib.Book05LocalClassFieldTheory.Chapter07.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- The canonical continuous multiplicative equivalence for a chosen abelian
Galois model.  When the model is maximal, its source is the full
`G_K^ab` used by the chapter. -/
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
  ext x
  rfl

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

/-- The reciprocity map for the chosen compatible finite Artin system, obtained
by applying the inverse-limit Galois equivalence to its compatible tuple.  A
maximality hypothesis is required when this chosen model is identified with
the full `G_K^ab`. -/
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
  change InfiniteGalois.proj L
      ((chapter07AbelianGaloisLimitEquiv K KAb)
        ((chapter07AbelianGaloisLimitEquiv K KAb).symm
          (S.toLimitHom x))) = S.artin L x
  rw [(chapter07AbelianGaloisLimitEquiv K KAb).apply_symm_apply]
  rfl

/-- Equivalent restriction formulation of the finite projection statement. -/
theorem chapter07_local_reciprocity_restricts_to_artin
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) (x : Kˣ) :
    AlgEquiv.restrictNormalHom L
        (chapter07LocalReciprocity S x) =
      S.artin L x := by
  change InfiniteGalois.proj L
      ((chapter07AbelianGaloisLimitEquiv K KAb)
        (chapter07LocalReciprocity S x)) = S.artin L x
  exact chapter07_finite_artin_is_the_reciprocity_projection S L x

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
  obtain ⟨f⟩ := hmax L
  let M : Chapter07FiniteAbelianIndex K KAb :=
    { f.fieldRange with
      finiteDimensional := f.toLinearMap.finiteDimensional_range
      isGalois := IsGalois.of_algEquiv (AlgHom.equivFieldRange f) }
  exact ⟨M, ⟨AlgHom.equivFieldRange f⟩⟩

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
  obtain ⟨M, ⟨e⟩⟩ :=
    chapter07_finite_abelian_levels_are_cofinal (K := K) (KAb := KAb) (L := L) hmax
  let eUnits : Lˣ →* Mˣ := Units.map e.toMonoidHom
  let eUnitsInv : Mˣ →* Lˣ := Units.map e.symm.toMonoidHom
  have heUnits_left (y : Lˣ) : eUnitsInv (eUnits y) = y := by
    ext
    simp [eUnits, eUnitsInv]
  have heUnits_right (y : Mˣ) : eUnits (eUnitsInv y) = y := by
    ext
    simp [eUnits, eUnitsInv]
  have hnorm_map (y : Lˣ) :
      chapter07NormHom (K := K) (L := M) (eUnits y) =
        chapter07NormHom (K := K) (L := L) y := by
    apply Units.ext
    change Algebra.norm K (e (y : L)) = Algebra.norm K (y : L)
    exact Algebra.norm_eq_of_algEquiv e (y : L)
  have hnorm :
      chapter07NormSubgroup (K := K) (L := M) =
        chapter07NormSubgroup (K := K) (L := L) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨eUnitsInv y, ?_⟩
      calc
        chapter07NormHom (K := K) (L := L) (eUnitsInv y) =
            chapter07NormHom (K := K) (L := M) (eUnits (eUnitsInv y)) := by
              rw [hnorm_map]
        _ = chapter07NormHom (K := K) (L := M) y := by rw [heUnits_right]
        _ = x := hy
    · rintro ⟨y, hy⟩
      refine ⟨eUnits y, ?_⟩
      calc
        chapter07NormHom (K := K) (L := M) (eUnits y) =
            chapter07NormHom (K := K) (L := L) y := hnorm_map y
        _ = x := hy
  let conjugate : Gal(M / K) ≃* Gal(L / K) :=
    { toFun := fun σ => (e.trans σ).trans e.symm
      invFun := fun τ => (e.symm.trans τ).trans e
      left_inv := by
        intro σ
        ext x
        simp [AlgEquiv.trans_apply]
      right_inv := by
        intro τ
        ext x
        simp [AlgEquiv.trans_apply]
      map_mul' := by
        intro σ τ
        ext x
        simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply] }
  let F : Kˣ →* Gal(L / K) := conjugate.toMonoidHom.comp (S.artin M)
  have hsurj : Function.Surjective F := by
    exact conjugate.surjective.comp (S.surjective M)
  have hker_artin : (S.artin M).ker =
      chapter07NormSubgroup (K := K) (L := L) :=
    (S.kernel_eq_norm M).trans hnorm
  have hker : F.ker = chapter07NormSubgroup (K := K) (L := L) := by
    ext x
    change conjugate (S.artin M x) = 1 ↔
      x ∈ chapter07NormSubgroup (K := K) (L := L)
    constructor
    · intro hx
      have hx' : S.artin M x = 1 := by
        apply conjugate.injective
        simpa using hx
      rw [← hker_artin]
      exact hx'
    · intro hx
      have hx' : S.artin M x = 1 := by
        change x ∈ (S.artin M).ker
        rw [hker_artin]
        exact hx
      rw [hx']
      exact conjugate.map_one
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective F hsurj)⟩

/-- The inverse-limit equivalence in the source notation
Galois-abelian-group equals Gal of the maximal abelian extension. -/
noncomputable def chapter07_galois_ab_is_the_inverse_limit_equiv
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (_hmax : chapter07IsMaximalAbelianExtension K KAb) :
    Gal(KAb / K) ≃ₜ*
      ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) :=
  chapter07AbelianGaloisLimitEquiv K KAb

/-- The inverse-limit statement in proposition form.  The maximality hypothesis
identifies the chosen model with the compositum of all finite abelian
extensions, rather than merely with the finite levels contained in an
arbitrary abelian Galois extension. -/
theorem chapter07_galois_ab_is_the_inverse_limit
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (hmax : chapter07IsMaximalAbelianExtension K KAb) :
    Nonempty
      (Gal(KAb / K) ≃ₜ*
        ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb)) :=
  ⟨chapter07_galois_ab_is_the_inverse_limit_equiv (K := K) (KAb := KAb) hmax⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
