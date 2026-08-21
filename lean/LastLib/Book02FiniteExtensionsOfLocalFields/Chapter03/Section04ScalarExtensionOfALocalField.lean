import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

universe uK uL uKp

noncomputable section

open scoped TensorProduct

open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

/-! ## 3.4. Scalar extension of a local field -/

/-- The scalar-extension algebra whose factors are studied below. -/
abbrev chapter03ScalarExtension
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Type _ :=
  L ⊗[K] K'

/-- The finite reduced profile of a scalar extension. -/
def chapter03FiniteReducedScalarExtension
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  letI : Algebra K' (chapter03ScalarExtension K L K') :=
    Algebra.TensorProduct.rightAlgebra
  Module.Finite K' (chapter03ScalarExtension K L K') ∧
    IsReduced (chapter03ScalarExtension K L K')

/-- A finite separable field extension remains finite reduced after base
change. -/
theorem chapter03_separable_scalar_extension_is_finite_reduced
    (K L K' : Type*) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [FiniteDimensional K K'] [Algebra.IsSeparable K L] :
    chapter03FiniteReducedScalarExtension K L K' := by
  let : Algebra K' (L ⊗[K] K') := Algebra.TensorProduct.rightAlgebra
  unfold chapter03FiniteReducedScalarExtension
  constructor
  · let : Module.Finite K' (K' ⊗[K] L) := Module.Finite.base_change K K' L
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight K K' L).toLinearEquiv
  · let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    let : Module.Finite K' (K' ⊗[K] L) := Module.Finite.base_change K K' L
    let : Module.Finite K' (L ⊗[K] K') :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight K K' L).toLinearEquiv
    let : Algebra.FormallyEtale K' (K' ⊗[K] L) := inferInstance
    let : Algebra.FormallyEtale K' (L ⊗[K] K') :=
      Algebra.FormallyEtale.of_equiv
        (Algebra.TensorProduct.commRight K K' L)
    exact Algebra.FormallyUnramified.isReduced_of_field K' _

/-- The reduced scalar extension is a finite product of field factors. -/
theorem chapter03_separable_scalar_extension_has_field_factors
    (K : Type uK) (L : Type uL) (K' : Type uKp) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [FiniteDimensional K K'] [Algebra.IsSeparable K L]
    (h : chapter03FiniteReducedScalarExtension K L K') :
    ∃ (I : Type (max uK (max uL uKp))) (_ : Finite I)
      (F : I → Type (max uK (max uL uKp)))
      (_ : ∀ i, Field (F i))
      (_ : ∀ i, Algebra K' (F i))
      (_ : ∀ i, FiniteDimensional K' (F i)),
      letI : Algebra K' (chapter03ScalarExtension K L K') :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (chapter03ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i)) := by
  let : Algebra K' (L ⊗[K] K') := Algebra.TensorProduct.rightAlgebra
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Algebra.FormallyEtale K' (K' ⊗[K] L) := inferInstance
  let : Module.Finite K' (K' ⊗[K] L) := Module.Finite.base_change K K' L
  let : Module.Finite K' (L ⊗[K] K') := by
    simpa [chapter03FiniteReducedScalarExtension] using h.1
  let : Algebra.FormallyEtale K' (L ⊗[K] K') :=
    Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight K K' L)
  have hEtale : Algebra.Etale K' (L ⊗[K] K') := by
    constructor
    · infer_instance
    · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rcases (Algebra.Etale.iff_exists_algEquiv_prod (K := K')
      (A := L ⊗[K] K')).mp hEtale with ⟨I, hI, F, hF, hA, e, hfinite⟩
  refine ⟨ULift.{max uK uL} I, inferInstance,
    (fun i : ULift.{max uK uL} I => ULift.{max uK uL} (F i.down)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((ULift.ringEquiv :
      ULift.{max uK uL} (F i.down) ≃+* F i.down).toMulEquiv.isField
        (Field.toIsField (F i.down))).toField
  · intro i
    infer_instance
  · intro i
    let : Module.Finite K' (F i.down) := (hfinite i.down).1
    exact Module.Finite.equiv
      (ULift.moduleEquiv.symm :
        F i.down ≃ₗ[K'] ULift.{max uK uL} (F i.down))
  · let eIndex : I ≃ ULift.{max uK uL} I := Equiv.ulift.symm
    let eIndexAlg : (∀ i, F i) ≃ₐ[K']
        (∀ i : ULift.{max uK uL} I, F (eIndex.symm i)) :=
      AlgEquiv.piCongrLeft' K' F eIndex
    let eLift : (∀ i : ULift.{max uK uL} I, F (eIndex.symm i)) ≃ₐ[K']
        (∀ i : ULift.{max uK uL} I, ULift.{max uK uL} (F (eIndex.symm i))) :=
      AlgEquiv.piCongrRight (fun i ↦
        (ULift.algEquiv (R := K') :
          ULift.{max uK uL} (F (eIndex.symm i)) ≃ₐ[K'] F (eIndex.symm i)).symm)
    have ee := e.trans (eIndexAlg.trans eLift)
    exact ⟨ee⟩

/- A factor of a scalar extension is an algebra over both the old left field
and the new base.  The compatibility equation exposes the left-field map
induced by the tensor factor, which is needed for valuation statements. -/
def chapter03ScalarExtensionFieldFactor
    (K L K' F : Type*) [CommRing K] [CommRing L] [CommRing K'] [Field F]
    [Algebra K L] [Algebra K K'] [Algebra K' F] [Algebra K F] [Algebra L F]
    [IsScalarTower K K' F] [IsScalarTower K L F] : Prop :=
  letI : Algebra K' (chapter03ScalarExtension K L K') :=
    Algebra.TensorProduct.rightAlgebra
  ∃ φ : chapter03ScalarExtension K L K' →ₐ[K'] F,
    Function.Surjective φ ∧
      (φ.restrictScalars K).comp
          (Algebra.TensorProduct.includeLeft :
            L →ₐ[K] chapter03ScalarExtension K L K') =
        IsScalarTower.toAlgHom K L F

/- The residue-field etale factorization lifts to the local statement: after
an unramified extension, every field factor remains unramified. -/
theorem chapter03_unramified_scalar_extension_field_factor_is_unramified
    (K L K' F Γ : Type*) [Field K] [Field L] [Field K'] [Field F]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K L] [Algebra K K'] [Algebra K' F] [Algebra K F]
    [Algebra L F]
    [IsScalarTower K K' F]
    [IsScalarTower K L F]
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional K' F]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (vK' : Valuation K' Γ) (vF : Valuation F Γ)
    [vK.HasExtension vL] [vK.HasExtension vK'] [vK'.HasExtension vF]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [Valuation.IsRankOneDiscrete vK']
    [Valuation.IsRankOneDiscrete vF]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunramified :
      chapterRamificationIndex vK.valuationSubring vL.valuationSubring
          (IsLocalRing.maximalIdeal vL.valuationSubring) = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueExtensionIsSeparable
          vK vL)
    (hfactor : chapter03ScalarExtensionFieldFactor K L K' F) :
    chapterRamificationIndex vK'.valuationSubring vF.valuationSubring
        (IsLocalRing.maximalIdeal vF.valuationSubring) = 1 ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueExtensionIsSeparable
        vK' vF := by
  sorry

/-- A finite factor over a complete rank-one base has a unique local
valuation extension. -/
theorem chapter03_complete_factor_has_unique_local_valuation
    {K' F Γ : Type u} [Field K'] [Field F]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K' F]
    (v : Valuation K' Γ) [Valuation.IsRankOneDiscrete v]
    [Algebra.IsAlgebraic K' F]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension v F := by
  unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension
  constructor
  · exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_valuation_extension_exists_as_heterogeneous v
  · intro W₁ W₂
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_henselian_valuation_has_unique_branch v
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_separated_local_ring_is_henselian hcomplete)
      W₁.valuation W₂.valuation W₁.isExtension W₂.isExtension

/- The source warning is made explicit: inseparable base change need not be a
product of fields, because nilpotents can appear. -/
def chapter03ScalarExtensionHasNilpotents
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  ¬ IsReduced (chapter03ScalarExtension K L K')

theorem chapter03_inseparable_self_scalar_extension_has_nilpotents
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hinseparable : ¬ Algebra.IsSeparable K L) :
    chapter03ScalarExtensionHasNilpotents K L L := by
  unfold chapter03ScalarExtensionHasNilpotents
  intro hred
  let : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite L (L ⊗[K] L) := Module.Finite.base_change K L L
  let : IsArtinianRing (L ⊗[K] L) := IsArtinianRing.of_finite L (L ⊗[K] L)
  let : IsReduced (L ⊗[K] L) := hred
  have hsemisimple : IsSemisimpleRing (L ⊗[K] L) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨e, he, hI⟩ :=
    @IsSemisimpleRing.ideal_eq_span_idempotent (L ⊗[K] L) _ hsemisimple
      (KaehlerDifferential.ideal K L)
  have heI : e ∈ KaehlerDifferential.ideal K L := by
    rw [hI]
    exact Ideal.subset_span
      (show e ∈ ({e} : Set (L ⊗[K] L)) from Set.mem_singleton e)
  have hle : Algebra.TensorProduct.lmul' K e = 0 := by
    exact heI
  have hformal : Algebra.FormallyUnramified K L := by
    rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
    refine ⟨1 - e, ?_, ?_⟩
    · intro s
      obtain ⟨x, hx⟩ :
          e ∣ (1 : L) ⊗ₜ[K] s - s ⊗ₜ[K] (1 : L) := by
        rw [← Ideal.mem_span_singleton, ← hI]
        exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal K s
      rw [hx, mul_comm, ← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]
    · rw [map_sub, map_one, hle, sub_zero]
  exact hinseparable ((Algebra.FormallyUnramified.iff_isSeparable K L).mp hformal)

/-- A scalar extension is a field only when its factor structure is trivial. -/
def chapter03ScalarExtensionIsAField
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  IsField (chapter03ScalarExtension K L K')

/-- The residue-field scalar extension in the unramified case is finite étale. -/
def chapter03ResidueScalarExtensionIsFiniteEtale
    (k l k' : Type*) [Field k] [Field l] [Field k']
    [Algebra k l] [Algebra k k'] : Prop :=
  letI : Algebra k' (l ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  Module.Finite k' (l ⊗[k] k') ∧ Algebra.Etale k' (l ⊗[k] k')

theorem chapter03_separable_residue_extension_is_stable_under_base_change
    (k l k' : Type*) [Field k] [Field l] [Field k']
    [Algebra k l] [Algebra k k'] [FiniteDimensional k l]
    [FiniteDimensional k k'] [Algebra.IsSeparable k l] :
    chapter03ResidueScalarExtensionIsFiniteEtale k l k' := by
  let : Algebra k' (l ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  unfold chapter03ResidueScalarExtensionIsFiniteEtale
  constructor
  · let : Module.Finite k' (k' ⊗[k] l) := Module.Finite.base_change k k' l
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight k k' l).toLinearEquiv
  · let : Algebra.FormallyEtale k l := Algebra.FormallyEtale.of_isSeparable k l
    let : Module.Finite k' (k' ⊗[k] l) := Module.Finite.base_change k k' l
    let : Algebra.FormallyEtale k' (k' ⊗[k] l) := inferInstance
    let : Algebra.FormallyEtale k' (l ⊗[k] k') :=
      Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight k k' l)
    let : Module.Finite k' (l ⊗[k] k') :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight k k' l).toLinearEquiv
    have hEtale : Algebra.Etale k' (l ⊗[k] k') := by
      constructor
      · infer_instance
      · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact hEtale

noncomputable instance chapter03BaseChangeCompositumLeftAlgebra
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L K' : IntermediateField K Ω) :
    Algebra (↥L) (↥(L ⊔ K')) :=
  (IntermediateField.inclusion le_sup_left).toAlgebra

noncomputable instance chapter03BaseChangeCompositumRightAlgebra
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L K' : IntermediateField K Ω) :
    Algebra (↥K') (↥(L ⊔ K')) :=
  (IntermediateField.inclusion le_sup_right).toAlgebra

/-- An extension of field valuations makes the upper valuation ring flat over
the lower one. -/
theorem chapter03_valuation_subring_extension_flat
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) [vK.HasExtension vL] :
    Module.Flat vK.valuationSubring vL.valuationSubring := by
  let : Module.IsTorsionFree vK.valuationSubring vL.valuationSubring := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x hax
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · right
      have hmap : algebraMap vK.valuationSubring vL.valuationSubring a ≠ 0 := by
        intro hzero
        apply ha
        have hz :
            algebraMap vK.valuationSubring vL.valuationSubring a =
              algebraMap vK.valuationSubring vL.valuationSubring
                (0 : vK.valuationSubring) := by
          simpa using hzero
        exact (Valuation.HasExtension.algebraMap_injective
          (vK := vK) (vA := vL)) hz
      apply (mul_eq_zero.mp ?_).resolve_left hmap
      simpa [Algebra.smul_def] using hax
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- The ramification indices and residue degrees on the two sides of a
common-codomain valuation square have the same products. -/
theorem chapter03_common_value_group_invariant_square
    {K L K' C Γ : Type*} [Field K] [Field L] [Field K'] [Field C]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K L] [Algebra K K'] [Algebra K C]
    [Algebra L C] [Algebra K' C]
    [IsScalarTower K L C] [IsScalarTower K K' C]
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional L C] [FiniteDimensional K' C]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (vK' : Valuation K' Γ) (vC : Valuation C Γ)
    [vK.HasExtension vL] [vK.HasExtension vK']
    [vK.HasExtension vC] [vL.HasExtension vC] [vK'.HasExtension vC] :
    (chapterRamificationIndex vK.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) =
        chapterRamificationIndex vK.valuationSubring vL.valuationSubring
            (IsLocalRing.maximalIdeal vL.valuationSubring) *
          chapterRamificationIndex vL.valuationSubring vC.valuationSubring
            (IsLocalRing.maximalIdeal vC.valuationSubring) ∧
      chapterRamificationIndex vK.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) =
        chapterRamificationIndex vK.valuationSubring vK'.valuationSubring
            (IsLocalRing.maximalIdeal vK'.valuationSubring) *
          chapterRamificationIndex vK'.valuationSubring vC.valuationSubring
            (IsLocalRing.maximalIdeal vC.valuationSubring)) ∧
    (chapterResidueDegree vK.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) =
        chapterResidueDegree vK.valuationSubring vL.valuationSubring
            (IsLocalRing.maximalIdeal vL.valuationSubring) *
          chapterResidueDegree vL.valuationSubring vC.valuationSubring
            (IsLocalRing.maximalIdeal vC.valuationSubring) ∧
      chapterResidueDegree vK.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) =
        chapterResidueDegree vK.valuationSubring vK'.valuationSubring
            (IsLocalRing.maximalIdeal vK'.valuationSubring) *
          chapterResidueDegree vK'.valuationSubring vC.valuationSubring
            (IsLocalRing.maximalIdeal vC.valuationSubring)) := by
  let : IsScalarTower vK.valuationSubring vL.valuationSubring
      vC.valuationSubring := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap K C (x : K) = algebraMap L C (algebraMap K L (x : K))
    exact IsScalarTower.algebraMap_apply K L C (x : K))
  let : IsScalarTower vK.valuationSubring vK'.valuationSubring
      vC.valuationSubring := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap K C (x : K) = algebraMap K' C (algebraMap K K' (x : K))
    exact IsScalarTower.algebraMap_apply K K' C (x : K))
  let : Module.Flat vL.valuationSubring vC.valuationSubring := by
    exact chapter03_valuation_subring_extension_flat vL vC
  let : Module.Flat vK'.valuationSubring vC.valuationSubring := by
    exact chapter03_valuation_subring_extension_flat vK' vC
  constructor
  · constructor
    · unfold chapterRamificationIndex
      exact Ideal.ramificationIdx_tower
        (IsLocalRing.maximalIdeal vL.valuationSubring)
        (IsLocalRing.maximalIdeal vC.valuationSubring)
    · unfold chapterRamificationIndex
      exact Ideal.ramificationIdx_tower
        (IsLocalRing.maximalIdeal vK'.valuationSubring)
        (IsLocalRing.maximalIdeal vC.valuationSubring)
  · constructor
    · unfold chapterResidueDegree
      exact Ideal.inertiaDeg_tower
        (IsLocalRing.maximalIdeal vL.valuationSubring)
        (IsLocalRing.maximalIdeal vC.valuationSubring)
    · unfold chapterResidueDegree
      exact Ideal.inertiaDeg_tower
        (IsLocalRing.maximalIdeal vK'.valuationSubring)
        (IsLocalRing.maximalIdeal vC.valuationSubring)

/- The source assertion is conditional on the two canonical directions of
local degree; arbitrary scalar extension can absorb ramification. -/
theorem chapter03_totally_ramified_extension_after_unramified_base_change
    {K Ω Γ : Type*} [Field K] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K Ω]
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K K']
    (vK : Valuation K Γ)
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (vL : Valuation (↥L) Γ)
    (vK' : Valuation (↥K') Γ)
    (vC : Valuation (↥(L ⊔ K')) Γ)
    [vK.HasExtension vL] [vK.HasExtension vK']
    [vK.HasExtension vC] [vL.HasExtension vC]
    [vK'.HasExtension vC]
    [IsScalarTower K (↥L) (↥(L ⊔ K'))]
    [IsScalarTower K (↥K') (↥(L ⊔ K'))]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [Valuation.IsRankOneDiscrete vK']
    [Valuation.IsRankOneDiscrete vC]
    [FiniteDimensional (↥L) (↥(L ⊔ K'))]
    [FiniteDimensional (↥K') (↥(L ⊔ K'))]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hL_total :
      chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) = 1)
    (hK'_unramified :
      chapterRamificationIndex vK.valuationSubring vK'.valuationSubring
          (IsLocalRing.maximalIdeal vK'.valuationSubring) = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueExtensionIsSeparable
          vK vK') :
    (L ⊓ K' = ⊥) ∧
      L.LinearDisjoint K' ∧
      chapterResidueDegree vK'.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) = 1 ∧
      (chapterRamificationIndex vL.valuationSubring vC.valuationSubring
          (IsLocalRing.maximalIdeal vC.valuationSubring) = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueExtensionIsSeparable
          vL vC) := by
  let eL := chapterRamificationIndex vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)
  let fL := chapterResidueDegree vK.valuationSubring vL.valuationSubring
    (IsLocalRing.maximalIdeal vL.valuationSubring)
  let eK' := chapterRamificationIndex vK.valuationSubring vK'.valuationSubring
    (IsLocalRing.maximalIdeal vK'.valuationSubring)
  let fK' := chapterResidueDegree vK.valuationSubring vK'.valuationSubring
    (IsLocalRing.maximalIdeal vK'.valuationSubring)
  let eLC := chapterRamificationIndex vL.valuationSubring vC.valuationSubring
    (IsLocalRing.maximalIdeal vC.valuationSubring)
  let fLC := chapterResidueDegree vL.valuationSubring vC.valuationSubring
    (IsLocalRing.maximalIdeal vC.valuationSubring)
  let fK'C := chapterResidueDegree vK'.valuationSubring vC.valuationSubring
    (IsLocalRing.maximalIdeal vC.valuationSubring)
  have hdegreeL : Module.finrank K L = eL * fL :=
    complete_extension_defectless_without_separability vK vL hcomplete
  have hdegreeK' : Module.finrank K K' = eK' * fK' :=
    complete_extension_defectless_without_separability vK vK' hcomplete
  have hdegreeC : Module.finrank K (↑(L ⊔ K')) =
      (eL * eLC) * (fL * fLC) := by
    rw [complete_extension_defectless_without_separability vK vC hcomplete]
    have hsquare := chapter03_common_value_group_invariant_square vK vL vK' vC
    rw [hsquare.1.1, hsquare.2.1]
  have hsquare := chapter03_common_value_group_invariant_square vK vL vK' vC
  have hfL : fL = 1 := hL_total
  have heK' : eK' = 1 := hK'_unramified.1
  have hfLC : fLC = fK' * fK'C := by
    have hresSquare := hsquare.2.1.symm.trans hsquare.2.2
    change fL * fLC = fK' * fK'C at hresSquare
    simpa only [hfL, one_mul] using hresSquare
  have hdegreeL' : Module.finrank K L = eL := by
    simpa only [hfL, Nat.mul_one] using hdegreeL
  have hdegreeK'' : Module.finrank K K' = fK' := by
    simpa only [heK', one_mul] using hdegreeK'
  have hdegreeC' : Module.finrank K (↑(L ⊔ K')) =
      (Module.finrank K L * Module.finrank K K') * (eLC * fK'C) := by
    rw [hdegreeC, hfL, hfLC, hdegreeL', hdegreeK'']
    ac_rfl
  have hbound : Module.finrank K (↑(L ⊔ K')) ≤
      Module.finrank K L * Module.finrank K K' :=
    IntermediateField.finrank_sup_le L K'
  have hfactor_le : eLC * fK'C ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left
    · rw [← hdegreeC']
      simpa only [Nat.mul_one] using hbound
    · exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hfactor_ne : eLC * fK'C ≠ 0 := by
    intro hzero
    rw [hzero, Nat.mul_zero] at hdegreeC'
    exact Module.finrank_pos.ne' hdegreeC'
  have hfactor_eq : eLC * fK'C = 1 := by omega
  have heLC : eLC = 1 := Nat.eq_one_of_mul_eq_one_right hfactor_eq
  have hfK'C : fK'C = 1 := Nat.eq_one_of_mul_eq_one_left hfactor_eq
  have hdegreeSup : Module.finrank K (↑(L ⊔ K')) =
      Module.finrank K L * Module.finrank K K' := by
    rw [hdegreeC', heLC, hfK'C]
    simp
  have hld : L.LinearDisjoint K' :=
    IntermediateField.LinearDisjoint.of_finrank_sup hdegreeSup
  have hinter : L ⊓ K' = ⊥ := hld.inf_eq_bot
  let _ : FiniteDimensional
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vL) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_residue_degree_finite vK vL
  let _ : PerfectField
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vL) :=
    Algebra.IsAlgebraic.perfectField
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK)
  let _ : FiniteDimensional
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vL)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vC) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_residue_degree_finite vL vC
  have hresidueSeparable :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueExtensionIsSeparable
        vL vC := by
    intro x
    exact Algebra.IsSeparable.isSeparable _ x
  exact ⟨hinter, hld, hfK'C, heLC, hresidueSeparable⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
