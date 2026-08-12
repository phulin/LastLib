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
  sorry

theorem chapter09_normSubgroup_mono_of_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [FiniteDimensional K L]
    [FiniteDimensional L M] [FiniteDimensional K M] :
    chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L := by
  sorry

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
  sorry

theorem chapter09_galoisInclusion_transitive
    (K L M Ks : Type*) [Field K] [Field L] [Field M] [Field Ks]
    [Algebra K L] [Algebra L M] [Algebra M Ks]
    [Algebra K M] [Algebra L Ks] [Algebra K Ks]
    [IsScalarTower K L M] [IsScalarTower L M Ks]
    [IsScalarTower K L Ks] [IsScalarTower K M Ks] :
    chapter09GaloisInclusion K M Ks =
      (chapter09GaloisInclusion K L Ks).comp
        (chapter09GaloisInclusion L M Ks) := by
  sorry

theorem chapter09_galoisInclusionAbelianization_transitive
    (K L M Ks : Type*) [Field K] [Field L] [Field M] [Field Ks]
    [Algebra K L] [Algebra L M] [Algebra M Ks]
    [Algebra K M] [Algebra L Ks] [Algebra K Ks]
    [IsScalarTower K L M] [IsScalarTower L M Ks]
    [IsScalarTower K L Ks] [IsScalarTower K M Ks] :
    chapter09GaloisInclusionAbelianization K M Ks =
      (chapter09GaloisInclusionAbelianization K L Ks).comp
        (chapter09GaloisInclusionAbelianization L M Ks) := by
  sorry

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
  sorry

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
  sorry

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

theorem chapter09_finite_quotient_reciprocity_compatibility
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    [IsAbelianGalois K M]
    (L : IntermediateField K M) [Normal K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional L M]
    (R_M : Chapter09FiniteAbelianReciprocity K M)
    (R_L : Chapter09FiniteAbelianReciprocity K L)
    (h : chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L) :
    (chapter09RestrictionMap K M L).comp R_M.quotientEquiv.toMonoidHom =
      R_L.quotientEquiv.toMonoidHom.comp (chapter09NormQuotientMap K M L h) := by
  sorry

theorem chapter09_finite_quotient_reciprocity_compatibility_apply
    (K M : Type*) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    [IsAbelianGalois K M]
    (L : IntermediateField K M) [Normal K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional L M]
    (R_M : Chapter09FiniteAbelianReciprocity K M)
    (R_L : Chapter09FiniteAbelianReciprocity K L)
    (h : chapter09NormSubgroup K M ≤ chapter09NormSubgroup K L)
    (x : Kˣ ⧸ chapter09NormSubgroup K M) :
    chapter09RestrictionMap K M L (R_M.quotientEquiv x) =
      R_L.quotientEquiv (chapter09NormQuotientMap K M L h x) := by
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
    DFunLike.congr_fun
      (chapter09_finite_quotient_reciprocity_compatibility K M L R_M R_L h) x

end

end LastLib.Book05LocalClassFieldTheory.Chapter09
