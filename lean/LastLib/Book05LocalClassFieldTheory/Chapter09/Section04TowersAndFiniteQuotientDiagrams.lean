import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

import LastLib.Book05LocalClassFieldTheory.Chapter09.Section03MultiplicativeInclusionCorrespondsToTransfer

namespace LastLib.Book05LocalClassFieldTheory.Chapter09

noncomputable section

/-!
## 9.4 Towers and finite quotient diagrams
-/

theorem chapter09_norm_hom_transitive
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter09NormHom K M =
      (chapter09NormHom K L).comp (chapter09NormHom L M) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  change Algebra.norm K (x : M) = Algebra.norm K (Algebra.norm L (x : M))
  exact (Algebra.norm_norm (R := K) (S := L) (a := (x : M))).symm

theorem chapter09_normSubgroup_mono_of_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L := by
  intro x hx
  change x ∈ (chapter09NormHom K M).range at hx
  rcases hx with ⟨y, rfl⟩
  rw [chapter09_norm_hom_transitive K L M]
  exact ⟨chapter09NormHom L M y, rfl⟩

theorem chapter09_normSubgroup_mem_of_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] (x : Kˣ)
    (hx : x ∈ chapter09NormSubgroup K M) :
    x ∈ chapter09NormSubgroup K L := by
  exact chapter09_normSubgroup_mono_of_tower K L M hx

theorem chapter09_field_inclusion_hom_transitive
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] :
    chapter09FieldInclusionHom K M =
      (chapter09FieldInclusionHom L M).comp (chapter09FieldInclusionHom K L) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  change algebraMap K M (x : K) = algebraMap L M (algebraMap K L (x : K))
  exact IsScalarTower.algebraMap_apply K L M (x : K)

theorem chapter09_galoisInclusion_transitive
    (K L M Ks : Type*) [Field K] [Field L] [Field M] [Field Ks]
    [Algebra K L] [Algebra L M] [Algebra M Ks]
    [Algebra K M] [Algebra L Ks] [Algebra K Ks]
    [IsScalarTower K L M] [IsScalarTower L M Ks]
    [IsScalarTower K L Ks] [IsScalarTower K M Ks] :
    chapter09GaloisInclusion K M Ks =
      (chapter09GaloisInclusion K L Ks).comp
        (chapter09GaloisInclusion L M Ks) := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  rfl

theorem chapter09_galoisInclusionAbelianization_transitive
    (K L M Ks : Type*) [Field K] [Field L] [Field M] [Field Ks]
    [Algebra K L] [Algebra L M] [Algebra M Ks]
    [Algebra K M] [Algebra L Ks] [Algebra K Ks]
    [IsScalarTower K L M] [IsScalarTower L M Ks]
    [IsScalarTower K L Ks] [IsScalarTower K M Ks] :
    chapter09GaloisInclusionAbelianization K M Ks =
      (chapter09GaloisInclusionAbelianization K L Ks).comp
        (chapter09GaloisInclusionAbelianization L M Ks) := by
  change Abelianization.map (chapter09GaloisInclusion K M Ks) =
    (Abelianization.map (chapter09GaloisInclusion K L Ks)).comp
      (Abelianization.map (chapter09GaloisInclusion L M Ks))
  calc
    Abelianization.map (chapter09GaloisInclusion K M Ks) =
        Abelianization.map
          ((chapter09GaloisInclusion K L Ks).comp
            (chapter09GaloisInclusion L M Ks)) := by
      rw [chapter09_galoisInclusion_transitive K L M Ks]
    _ = (Abelianization.map (chapter09GaloisInclusion K L Ks)).comp
        (Abelianization.map (chapter09GaloisInclusion L M Ks)) := by
      symm
      exact Abelianization.map_comp
        (f := chapter09GaloisInclusion L M Ks)
        (g := chapter09GaloisInclusion K L Ks)

theorem chapter09_transferAlong_transitive
    {G₀ G₁ G₂ : Type*} [Group G₀] [Group G₁] [Group G₂]
    (f : G₁ →* G₀) (g : G₂ →* G₁)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : f.range.FiniteIndex) (hgg : g.range.FiniteIndex)
    (hcomp : (f.comp g).range.FiniteIndex) :
    chapter09TransferAlong (f.comp g) (hf.comp hg) hcomp =
      (chapter09TransferAlong g hg hgg).comp
    (chapter09TransferAlong f hf hfg) := by
  sorry

/- The two functoriality squares compose in a tower.  This generic form makes
the word "stack" in the source precise without choosing a second reciprocity
system for a three-level tower. -/

theorem chapter09_norm_reciprocity_squares_stack
    {C_K C_L C_M G_K G_L G_M : Type*}
    [CommGroup C_K] [CommGroup C_L] [CommGroup C_M]
    [CommGroup G_K] [CommGroup G_L] [CommGroup G_M]
    (normLK : C_L →* C_K) (normML : C_M →* C_L)
    (inclLK : G_L →* G_K) (inclML : G_M →* G_L)
    (recK : C_K →* G_K) (recL : C_L →* G_L) (recM : C_M →* G_M)
    (hLK : recK.comp normLK = inclLK.comp recL)
    (hML : recL.comp normML = inclML.comp recM) :
    recK.comp (normLK.comp normML) =
      (inclLK.comp inclML).comp recM := by
  apply MonoidHom.ext
  intro x
  change recK (normLK (normML x)) = inclLK (inclML (recM x))
  calc
    recK (normLK (normML x)) = inclLK (recL (normML x)) :=
      DFunLike.congr_fun hLK (normML x)
    _ = inclLK (inclML (recM x)) := by
      exact congrArg inclLK (DFunLike.congr_fun hML x)

theorem chapter09_transfer_reciprocity_squares_stack
    {C_K C_L C_M G_K G_L G_M : Type*}
    [CommGroup C_K] [CommGroup C_L] [CommGroup C_M]
    [CommGroup G_K] [CommGroup G_L] [CommGroup G_M]
    (inclKL : C_K →* C_L) (inclLM : C_L →* C_M)
    (transferKL : G_K →* G_L) (transferLM : G_L →* G_M)
    (recK : C_K →* G_K) (recL : C_L →* G_L) (recM : C_M →* G_M)
    (hKL : recL.comp inclKL = transferKL.comp recK)
    (hLM : recM.comp inclLM = transferLM.comp recL) :
    recM.comp (inclLM.comp inclKL) =
      (transferLM.comp transferKL).comp recK := by
  apply MonoidHom.ext
  intro x
  change recM (inclLM (inclKL x)) = transferLM (transferKL (recK x))
  calc
    recM (inclLM (inclKL x)) = transferLM (recL (inclKL x)) :=
      DFunLike.congr_fun hLM (inclKL x)
    _ = transferLM (transferKL (recK x)) := by
      exact congrArg transferLM (DFunLike.congr_fun hKL x)

/-- The natural quotient map induced by an inclusion of normal subgroups. -/
def chapter09QuotientMapOfLe
    {A : Type*} [CommGroup A] {N M : Subgroup A} (h : N ≤ M) :
    A ⧸ N →* A ⧸ M :=
  QuotientGroup.map N M (MonoidHom.id A) (by simpa using h)

theorem chapter09QuotientMapOfLe_mk
    {A : Type*} [CommGroup A] {N M : Subgroup A} (h : N ≤ M) (x : A) :
    chapter09QuotientMapOfLe h (QuotientGroup.mk' N x) = QuotientGroup.mk' M x := by
  rfl

/-!
For an intermediate field `L` of `M/K`, the following declarations spell out
the quotient square in the source.  The normality and finite-dimensionality
instances are kept explicit at this interface; the preceding finite abelian
Galois API supplies them for the intended applications.
-/

theorem chapter09_intermediate_normSubgroup_mono
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (L : IntermediateField K M) [FiniteDimensional K L]
    [FiniteDimensional L M] :
    chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L := by
  exact chapter09_normSubgroup_mono_of_tower K L M

def chapter09NormQuotientMap
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (L : IntermediateField K M) [FiniteDimensional K L]
    [FiniteDimensional L M]
    (h : chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L) :
    (Kˣ ⧸ chapter09NormSubgroup K M) →*
      (Kˣ ⧸ chapter09NormSubgroup K L) :=
  chapter09QuotientMapOfLe h

theorem chapter09NormQuotientMap_ker
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (L : IntermediateField K M) [FiniteDimensional K L]
    [FiniteDimensional L M]
    (h : chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L) :
    (chapter09NormQuotientMap K M L h).ker =
      Subgroup.map (QuotientGroup.mk' (chapter09NormSubgroup K M))
        (chapter09NormSubgroup K L) := by
  simpa [chapter09NormQuotientMap, chapter09QuotientMapOfLe] using
    (QuotientGroup.ker_map
      (N := chapter09NormSubgroup K M)
      (M := chapter09NormSubgroup K L)
      (MonoidHom.id Kˣ) (by simpa using h))

/-- Restriction of a normal automorphism to the intermediate field. -/
def chapter09RestrictionMap
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Normal K L] :
    Gal(M / K) →* Gal(L / K) :=
  AlgEquiv.restrictNormalHom L

theorem chapter09_restriction_kernel_eq_fixingSubgroup
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Normal K L] :
    (chapter09RestrictionMap K M L).ker = L.fixingSubgroup := by
  simpa [chapter09RestrictionMap] using
    (IntermediateField.restrictNormalHom_ker L)

/-- The restriction kernel is the Galois group of the upper extension over `L`. -/
noncomputable def chapter09RestrictionKernelEquiv
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    (L : IntermediateField K M) [Normal K L] :
    (chapter09RestrictionMap K M L).ker ≃* Gal(M / L) :=
  (MulEquiv.subgroupCongr
      (chapter09_restriction_kernel_eq_fixingSubgroup K M L)).trans
    (IntermediateField.fixingSubgroupEquiv L)

/-!
The two vertical maps and the two horizontal reciprocity equivalences form
the finite quotient diagram of §9.4.
-/

/- A common normalized absolute reciprocity map is included in the theorem
  interface so that both finite quotients are actual restrictions of one
  compatible system, rather than independently chosen quotient labels. -/

structure Chapter09FiniteReciprocityTower
    (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsAbelianGalois K M]
    [Fintype (Gal(M / K))]
    (L : IntermediateField K M) [Normal K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))] [FiniteDimensional L M] where
  upperReciprocity : Chapter09FiniteAbelianReciprocity K M
  lowerReciprocity : Chapter09FiniteAbelianReciprocity K L
  normSubgroup_mono : chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L

theorem chapter09_finite_quotient_reciprocity_compatibility
    (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    [IsAbelianGalois K M]
    [Fintype (Gal(M / K))]
    (L : IntermediateField K M) [Normal K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [FiniteDimensional L M]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra M Ks] [Algebra L Ks]
    [IsScalarTower K M Ks] [IsScalarTower K L Ks]
    [IsScalarTower L M Ks]
    (reciprocity : Kˣ →* Abelianization (Gal(Ks / K)))
    (A : Chapter09AbsoluteReciprocityNormalization K Ks reciprocity)
    (T : Chapter09FiniteReciprocityTower K M L) :
    (chapter09RestrictionMap K M L).comp
        T.upperReciprocity.quotientEquiv.toMonoidHom =
      T.lowerReciprocity.quotientEquiv.toMonoidHom.comp
        (chapter09NormQuotientMap K M L T.normSubgroup_mono) := by
  sorry

theorem chapter09_finite_quotient_reciprocity_compatibility_apply
    (K M : Type) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    [IsAbelianGalois K M]
    [Fintype (Gal(M / K))]
    (L : IntermediateField K M) [Normal K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    [FiniteDimensional L M]
    (Ks : Type) [Field Ks]
    [Algebra K Ks] [Algebra M Ks] [Algebra L Ks]
    [IsScalarTower K M Ks] [IsScalarTower K L Ks]
    [IsScalarTower L M Ks]
    (reciprocity : Kˣ →* Abelianization (Gal(Ks / K)))
    (A : Chapter09AbsoluteReciprocityNormalization K Ks reciprocity)
    (T : Chapter09FiniteReciprocityTower K M L)
    (x : Kˣ ⧸ chapter09NormSubgroup K M) :
    chapter09RestrictionMap K M L
        (T.upperReciprocity.quotientEquiv x) =
      T.lowerReciprocity.quotientEquiv
        (chapter09NormQuotientMap K M L T.normSubgroup_mono x) := by
  change
    ((chapter09RestrictionMap K M L).comp
        T.upperReciprocity.quotientEquiv.toMonoidHom) x =
      (T.lowerReciprocity.quotientEquiv.toMonoidHom.comp
        (chapter09NormQuotientMap K M L T.normSubgroup_mono)) x
  exact DFunLike.congr_fun
    (chapter09_finite_quotient_reciprocity_compatibility K M L Ks reciprocity A T) x

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
