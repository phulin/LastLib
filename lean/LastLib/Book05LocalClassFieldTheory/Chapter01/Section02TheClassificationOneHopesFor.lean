import LastLib.Book05LocalClassFieldTheory.Chapter01.Section01WhatKindOfLocalFieldIsMeant
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section07ContinuityOfEmbeddings

namespace LastLib.Book05LocalClassFieldTheory.Chapter01

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Set
open scoped BigOperators Pointwise Topology WithZero IsMulCommutative

/-! ## 1.2. The classification one hopes for -/

/-- The norm is a continuous homomorphism on multiplicative groups. -/
theorem chapter01_norm_continuous
    (K L : Type*) [NormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] :
    Continuous (chapter01NormHom K L) := by
  change Continuous (Units.map (Algebra.norm K (S := L)))
  exact
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_trace_and_norm_are_continuous
      (K := K) (L := L)).2.units_map _

/-- For a finite abelian extension of local fields, the norm subgroup is open
and has finite index.  The local hypotheses are explicit because the generic
norm homomorphism above does not carry a valuation topology. -/
theorem chapter01_abelian_norm_subgroup_is_open_and_finite_index
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hLlocal : Chapter01LocalField vL)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (hplace : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    IsOpen (chapter01NormSubgroup K L : Set Kˣ) ∧
    (chapter01NormSubgroup K L).FiniteIndex := by
  sorry

/-- A continuous image of a compact source set is closed in a Hausdorff target.
The full field-unit group of a local field is not compact, so this criterion is
stated for an explicitly chosen compact source set rather than incorrectly
assuming compactness of `Lˣ`. -/
theorem chapter01_norm_image_is_closed_of_compact_source
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [TopologicalSpace Lˣ] [TopologicalSpace Kˣ]
    [T2Space Kˣ]
    (C : Set Lˣ) (hcompact : IsCompact C)
    (hcontinuous : Continuous (chapter01NormHom K L)) :
    IsClosed ((chapter01NormHom K L) '' C) := by
  exact (hcompact.image hcontinuous).isClosed

/-- The local norm-index formula. -/
theorem chapter01_norm_index_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hLlocal : Chapter01LocalField vL)
    (hplace : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    (chapter01NormSubgroup K L).index = Module.finrank K L := by
  sorry

/-- A finite-level Artin map attached to a quotient equivalence. -/
def chapter01FiniteArtinMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group (Gal(L / K))]
    (e : Chapter01NormQuotient K L ≃* Gal(L / K)) : Kˣ →* Gal(L / K) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (chapter01NormSubgroup K L))

theorem chapter01_finite_artin_map_eq_composition
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group (Gal(L / K))]
    (e : Chapter01NormQuotient K L ≃* Gal(L / K)) :
    e.toMonoidHom.comp (QuotientGroup.mk' (chapter01NormSubgroup K L)) =
      chapter01FiniteArtinMap e :=
  rfl

/-- The kernel of the finite Artin map is the norm subgroup. -/
theorem chapter01_finite_artin_map_kernel
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group (Gal(L / K))]
    (e : Chapter01NormQuotient K L ≃* Gal(L / K)) :
    (chapter01FiniteArtinMap e).ker = chapter01NormSubgroup K L := by
  ext x
  simp [chapter01FiniteArtinMap]

/-- The finite Artin map is onto. -/
theorem chapter01_finite_artin_map_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group (Gal(L / K))]
    (e : Chapter01NormQuotient K L ≃* Gal(L / K)) :
    Function.Surjective (chapter01FiniteArtinMap e) := by
  exact e.surjective.comp (QuotientGroup.mk'_surjective (chapter01NormSubgroup K L))

/-- The finite reciprocity isomorphism for an abelian finite extension. -/
theorem chapter01_finite_reciprocity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] [IsMulCommutative (Gal(L / K))]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hLlocal : Chapter01LocalField vL)
    (hplace : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    Nonempty (Chapter01NormQuotient K L ≃* Gal(L / K)) := by
  sorry

/-- The maximal abelian extension realizes every open finite-index subgroup. -/
theorem chapter01_local_existence_theorem
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (D : Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    (H : Chapter01OpenFiniteIndexSubgroup Kˣ) :
    ∃! L : Chapter01FiniteAbelianIndex K D.extension,
      chapter01NormSubgroup K L = H.1 := by
  sorry

/-- The unique finite abelian level selected by an open subgroup. -/
noncomputable def chapter01ExtensionOfOpenSubgroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (D : Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    (H : Chapter01OpenFiniteIndexSubgroup Kˣ) :
    Chapter01FiniteAbelianIndex K D.extension :=
  (chapter01_local_existence_theorem vK hKlocal hbasis D H).choose

theorem chapter01_norm_of_extension_of_open_subgroup
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (D : Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    (H : Chapter01OpenFiniteIndexSubgroup Kˣ) :
    chapter01NormSubgroup K (chapter01ExtensionOfOpenSubgroup vK hKlocal hbasis D H) = H.1 :=
  ((chapter01_local_existence_theorem vK hKlocal hbasis D H).choose_spec).1

/-- Uniqueness of the extension attached to an open subgroup. -/
theorem chapter01_extension_of_open_subgroup_unique
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (D : Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    (H : Chapter01OpenFiniteIndexSubgroup Kˣ)
    (L : Chapter01FiniteAbelianIndex K D.extension)
    (hL : chapter01NormSubgroup K L = H.1) :
    L = chapter01ExtensionOfOpenSubgroup vK hKlocal hbasis D H :=
  (chapter01_local_existence_theorem vK hKlocal hbasis D H).unique hL
    (chapter01_norm_of_extension_of_open_subgroup vK hKlocal hbasis D H)

/-- Inclusion of finite abelian levels reverses inclusion of norm groups. -/
theorem chapter01_norm_inclusion_reversing
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (vK : AddValuation K (WithTop ℤ))
    (hKlocal : Chapter01LocalField vK)
    (hbasis : Chapter01FieldUnitFiltrationNeighborhoodBasis vK)
    (D : Chapter01MaximalAbelianExtensionData K)
    [IsAbelianGalois K D.extension]
    {L₁ L₂ : Chapter01FiniteAbelianIndex K D.extension} :
    L₁ ≤ L₂ ↔ chapter01NormSubgroup K L₂ ≤ chapter01NormSubgroup K L₁ := by
  sorry

/-- The finite Artin system descends each map through its norm quotient. -/
noncomputable def chapter01FiniteReciprocityQuotientHom
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) :
    Chapter01NormQuotient K L →* Gal(L / K) :=
  QuotientGroup.lift (chapter01NormSubgroup K L) (S.artin L) (by
    rw [← S.kernel_eq_norm L])

theorem chapter01_finite_artin_system_kernel_eq_norm
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) :
    (S.artin L).ker = chapter01NormSubgroup K L :=
  S.kernel_eq_norm L

theorem chapter01_finite_artin_kernel_is_open
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsAbelianGalois K KAb]
    (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb)
    (hopen : IsOpen (chapter01NormSubgroup K L : Set Kˣ)) :
    IsOpen ((S.artin L).ker : Set Kˣ) := by
  rw [chapter01_finite_artin_system_kernel_eq_norm S L]
  exact hopen

theorem chapter01_finite_artin_system_compatible
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    {L₁ L₂ : (FiniteGaloisIntermediateField K KAb)ᵒᵖ}
    (f : L₁ ⟶ L₂) (x : Kˣ) :
    (finGaloisGroupMap f).hom (S.artin L₁.unop x) = S.artin L₂.unop x :=
  S.compatible f x

/-- The descended finite map composed with the quotient map is the Artin map. -/
theorem chapter01FiniteReciprocityQuotientHom_comp_mk
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) :
    (chapter01FiniteReciprocityQuotientHom S L).comp
        (QuotientGroup.mk' (chapter01NormSubgroup K L)) = S.artin L := by
  sorry

/-- The quotient equivalence obtained from the finite Artin system. -/
noncomputable def chapter01FiniteReciprocityEquiv
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) :
    Chapter01NormQuotient K L ≃* Gal(L / K) := by
  let hker : (S.artin L).ker = chapter01NormSubgroup K L :=
    S.kernel_eq_norm L
  exact
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (S.artin L) (S.surjective L))

/-- The finite Artin maps as a compatible point of the Galois inverse limit. -/
noncomputable def Chapter01FiniteArtinSystem.toLimitHom
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb) :
    Kˣ →* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb) where
  toFun x :=
    { val := fun L => S.artin L.unop x
      property := by
        intro L₁ L₂ f
        exact S.compatible f x }
  map_one' := by
    apply Subtype.ext
    funext L
    exact map_one (S.artin L.unop)
  map_mul' x y := by
    apply Subtype.ext
    funext L
    exact map_mul (S.artin L.unop) x y

/-- The local reciprocity map assembled from the compatible finite levels. -/
noncomputable def chapter01LocalReciprocity
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb) :
    Kˣ →* Gal(KAb / K) :=
  (chapter01AbelianGaloisLimitEquiv K KAb).symm.toMulEquiv.toMonoidHom.comp
    S.toLimitHom

/-- The finite projection of local reciprocity is the prescribed Artin map. -/
theorem chapter01_finite_artin_is_reciprocity_projection
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) (x : Kˣ) :
    InfiniteGalois.proj L
        (chapter01AbelianGaloisLimitEquiv K KAb
          (chapter01LocalReciprocity S x)) = S.artin L x := by
  sorry

/-- Local reciprocity is continuous once the finite norm kernels are open. -/
theorem chapter01_local_reciprocity_continuous
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ)) :
    Continuous (chapter01LocalReciprocity S) := by
  sorry

/-- Every finite projection of local reciprocity is onto. -/
theorem chapter01_local_reciprocity_surjective_on_finite_level
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (L : Chapter01FiniteAbelianIndex K KAb) :
    Function.Surjective (S.artin L) :=
  S.surjective L

/-- The image of local reciprocity is dense in the profinite abelian Galois
group. -/
theorem chapter01_local_reciprocity_dense
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb) :
    DenseRange (chapter01LocalReciprocity S) := by
  sorry

/-- The target is the canonical inverse limit of its finite Galois quotients. -/
theorem chapter01_galois_ab_is_inverse_limit
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    Nonempty
      (Gal(KAb / K) ≃ₜ*
        ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K KAb)) :=
  ⟨chapter01AbelianGaloisLimitEquiv K KAb⟩

/-- The open-indexed completion admits an extension of local reciprocity once
all finite norm levels are open. -/
theorem chapter01_open_completion_artin_extension_exists
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ)) :
    ∃ F : Chapter01OpenProfiniteCompletion Kˣ →* Gal(KAb / K),
      Continuous F ∧
        ∀ x,
          F (chapter01OpenProfiniteCompletionEta Kˣ x) =
            chapter01LocalReciprocity S x := by
  sorry

noncomputable def chapter01CompletedReciprocity
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ)) :
    Chapter01OpenProfiniteCompletion Kˣ →* Gal(KAb / K) :=
  (chapter01_open_completion_artin_extension_exists S hopen).choose

/-- The completed map extends local reciprocity on the canonical copy of
`Kˣ`. -/
theorem chapter01_completed_reciprocity_extends_local
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ))
    (x : Kˣ) :
    chapter01CompletedReciprocity S hopen
        (chapter01OpenProfiniteCompletionEta Kˣ x) =
      chapter01LocalReciprocity S x := by
  exact (chapter01_open_completion_artin_extension_exists S hopen).choose_spec.2 x

/-- The completed reciprocity map is continuous. -/
theorem chapter01_completed_reciprocity_continuous
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ)) :
    Continuous (chapter01CompletedReciprocity S hopen) := by
  exact (chapter01_open_completion_artin_extension_exists S hopen).choose_spec.1

/-- The topology-sensitive completion is identified with the abelian Galois
target when the finite norm levels realize every open finite-index subgroup. -/
theorem chapter01_completed_reciprocity_is_topological_equivalence
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter01FiniteArtinSystem K KAb)
    (hopen : ∀ L : Chapter01FiniteAbelianIndex K KAb,
      IsOpen (chapter01NormSubgroup K L : Set Kˣ))
    (hExist : ∀ H : Chapter01OpenFiniteIndexSubgroup Kˣ,
      ∃! L : Chapter01FiniteAbelianIndex K KAb,
        chapter01NormSubgroup K L = H.1) :
    ∃ e : Chapter01OpenProfiniteCompletion Kˣ ≃ₜ* Gal(KAb / K),
      ∀ x, e x = chapter01CompletedReciprocity S hopen x := by
  sorry

/-- The abelian Galois target is compact in the profinite topology. -/
theorem chapter01_reciprocity_target_is_compact
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    IsCompact (Set.univ : Set (Gal(KAb / K))) := by
  exact isCompact_univ

/-- A noncompact source cannot be topologically equivalent to the compact
profinite target. -/
theorem chapter01_reciprocity_not_a_topological_equivalence
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (hnoncompact : NoncompactSpace Kˣ)
    (hcompact : IsCompact (Set.univ : Set (Gal(KAb / K)))) :
    ¬ Nonempty (Kˣ ≃ₜ* Gal(KAb / K)) := by
  exact fun ⟨e⟩ =>
    (not_compactSpace_iff.mpr hnoncompact) ⟨by
      have himage := hcompact.image e.symm.continuous_toFun
      have hrange : Set.range e.symm.toFun = (Set.univ : Set Kˣ) :=
        Set.range_eq_univ.mpr e.symm.surjective
      simpa only [Set.image_univ, hrange] using himage⟩

end

end LastLib.Book05LocalClassFieldTheory.Chapter01
