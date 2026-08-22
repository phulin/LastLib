import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import LastLib.Book04AdelesAndIdeles.Chapter10.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Section04FinitenessOfRayClassGroups
import LastLib.Book04AdelesAndIdeles.Chapter11.Section05OpenCompactSubgroups

/-!
# Chapter 14: shared interfaces

This file contains the canonical adelic objects supplied by Mathlib together with the small
interfaces needed to state the later class-field-theoretic assertions.  The latter are deliberately
data-bearing interfaces: the construction of the global reciprocity map and the local embeddings
belongs to the later reciprocity chapters.
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

open CategoryTheory
open scoped NNReal NumberField

/-! ## The canonical adelic objects -/

abbrev chapter14FiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  Chapter09.Chapter09FiniteAdele K

abbrev chapter14AdeleRing (K : Type*) [Field K] [NumberField K] :=
  Chapter09.Chapter09Adele K

abbrev chapter14FiniteIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (Chapter09.Chapter09FiniteAdele K)ˣ

abbrev chapter14InfiniteIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (Chapter09.Chapter09InfiniteAdele K)ˣ

abbrev chapter14IdeleGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter09.Chapter09Idele K

abbrev chapter14IdealClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (𝓞 K)

/-- The product decomposition of an idele into its infinite and finite parts. -/
def chapter14IdeleProductEquiv (K : Type*) [Field K] [NumberField K] :
    chapter14IdeleGroup K ≃* 
      chapter14InfiniteIdeleGroup K × chapter14FiniteIdeleGroup K :=
  Chapter09.chapter09IdeleProductEquiv K

theorem chapter14_finite_idele_integral_tail {K : Type*} [Field K] [NumberField K]
    (a : chapter14FiniteIdeleGroup K) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
      in Filter.cofinite,
      Valued.v (RestrictedProduct.unitsEquiv _ a v).1 = 1 := by
  exact IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a

/-- Principal ideles are the units obtained from the diagonal field embedding. -/
def chapter14PrincipalIdeleEmbedding (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter14IdeleGroup K :=
  Chapter09.chapter09PrincipalIdele K

abbrev chapter14PrincipalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :=
  Chapter09.chapter09PrincipalIdeleSubgroup K

abbrev chapter14IdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter09.Chapter09IdeleClassGroup K

def chapter14IdeleClassMap (K : Type*) [Field K] [NumberField K] :
    chapter14IdeleGroup K →* chapter14IdeleClassGroup K :=
  QuotientGroup.mk' _

@[simp]
theorem chapter14IdeleClassMap_apply (K : Type*) [Field K] [NumberField K]
    (x : chapter14IdeleGroup K) :
    chapter14IdeleClassMap K x = QuotientGroup.mk x := rfl

theorem chapter14_principal_idele_subgroup_eq_chapter11
    {K : Type*} [Field K] [NumberField K] :
    chapter14PrincipalIdeleSubgroup K =
      Chapter11.chapter11PrincipalIdeleSubgroup (K := K) := by
  rfl

/-! ## Finite levels of the idele class group -/

abbrev chapter14AbelianGaloisGroup (K : Type*) [Field K] :=
  Field.absoluteGaloisGroupAbelianization K

/-- Open finite-index normal subgroups, the indexing objects used by the book's completion. -/
def Chapter14OpenFiniteIndexSubgroup (C : Type*) [Group C] [TopologicalSpace C] :=
  {U : FiniteIndexNormalSubgroup C // IsOpen (U : Set C)}

instance chapter14OpenFiniteIndexSubgroupPreorder (C : Type*) [Group C]
    [TopologicalSpace C] : Preorder (Chapter14OpenFiniteIndexSubgroup C) :=
  { le := fun U V => U.1 ≤ V.1
    le_refl := fun U => le_refl U.1
    le_trans := fun _ _ _ hUV hVW => le_trans hUV hVW }

def chapter14OpenFiniteIndexQuotientDiagram (C : Type*) [Group C] [TopologicalSpace C] :
    Chapter14OpenFiniteIndexSubgroup C ⥤ FiniteGrp where
  obj U := FiniteGrp.of (C ⧸ U.1.toSubgroup)
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id C) (by
    intro x hx
    exact f.le hx)
  map_id _ := by ext ⟨x⟩; rfl
  map_comp _ _ := by ext ⟨x⟩; rfl

def chapter14OpenFiniteIndexQuotientDiagramProfinite (C : Type*) [Group C]
    [TopologicalSpace C] :
    Chapter14OpenFiniteIndexSubgroup C ⥤ ProfiniteGrp :=
  chapter14OpenFiniteIndexQuotientDiagram C ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The completion formed from open finite-index quotients of a topological group. -/
noncomputable def chapter14ProfiniteCompletion (C : Type*) [Group C] [TopologicalSpace C] :
    ProfiniteGrp :=
  ProfiniteGrp.limit (chapter14OpenFiniteIndexQuotientDiagramProfinite C)

/-- The canonical map into the open finite-level completion. -/
def chapter14ProfiniteCompletionMap (C : Type*) [Group C] [TopologicalSpace C] :
    C →* chapter14ProfiniteCompletion C :=
  { toFun := fun x =>
      ⟨fun U => QuotientGroup.mk x, fun _ _ _ => rfl⟩
    map_one' := by
      apply ProfiniteGrp.limit_ext
      intro U
      rfl
    map_mul' := by
      intro x y
      apply ProfiniteGrp.limit_ext
      intro U
      rfl }

def chapter14ProfiniteCompletionProjection (C : Type*) [Group C] [TopologicalSpace C]
    (U : Chapter14OpenFiniteIndexSubgroup C) :
    chapter14ProfiniteCompletion C →* C ⧸ U.1.toSubgroup :=
  (((ProfiniteGrp.limitCone
      (chapter14OpenFiniteIndexQuotientDiagramProfinite C)).π.app U).hom).toMonoidHom

@[simp]
theorem chapter14ProfiniteCompletionProjection_map (C : Type*) [Group C]
    [TopologicalSpace C] (U : Chapter14OpenFiniteIndexSubgroup C) (x : C) :
    chapter14ProfiniteCompletionProjection C U
        (chapter14ProfiniteCompletionMap C x) = QuotientGroup.mk x := by
  rfl

abbrev chapter14IdeleClassProfiniteCompletion (K : Type*) [Field K] [NumberField K] :=
  chapter14ProfiniteCompletion (chapter14IdeleClassGroup K)

def chapter14GlobalReciprocityStatement (K : Type*) [Field K] [NumberField K] : Prop :=
  Nonempty (chapter14IdeleClassProfiniteCompletion K ≃ₜ*
    chapter14AbelianGaloisGroup K)

/-! The two standard choices for the Frobenius normalization. -/

inductive Chapter14FrobeniusConvention
  | arithmetic
  | geometric

/-!
The next structure is the one genuinely missing from the earlier chapters: an embedding of each
local multiplicative factor into the global idele group.  The ray levels themselves are taken
from Chapter 11 below, rather than being represented by a second arbitrary family of subgroups.
-/

structure Chapter14LocalComponentData (K : Type*) [Field K] [NumberField K] where
  finiteComponent : ∀ v : NumberField.FinitePlace K,
    (v.maximalIdeal.adicCompletion K)ˣ →* chapter14IdeleGroup K
  finiteComponent_continuous :
    ∀ v, Continuous (finiteComponent v)
  finiteComponent_injective :
    ∀ v, Function.Injective (finiteComponent v)
  infiniteComponent : ∀ w : NumberField.InfinitePlace K,
    (w.Completion)ˣ →* chapter14IdeleGroup K
  infiniteComponent_continuous :
    ∀ w, Continuous (infiniteComponent w)
  infiniteComponent_injective :
    ∀ w, Function.Injective (infiniteComponent w)

/-! A finite level records the open idele subgroup and the finiteness of its quotient after
adjoining principal ideles.  The source's stronger neighborhood hypotheses are stated separately
below, so arbitrary quotient levels are not silently treated as ray neighborhoods. -/
structure Chapter14FiniteLevel (K : Type*) [Field K] [NumberField K] where
  subgroup : Subgroup (chapter14IdeleGroup K)
  isOpen' : IsOpen (subgroup : Set (chapter14IdeleGroup K))
  finiteIndex' :
    (chapter14PrincipalIdeleSubgroup K ⊔ subgroup).FiniteIndex

/-! These predicates spell out the two extra hypotheses on an open level used by the source's
cofinality argument.  They are kept separate from the quotient data so that an arbitrary finite
quotient level cannot be mistaken for a ray neighborhood. -/
def chapter14ContainsPositiveMagnitudeDirections
    {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) : Prop :=
  ∀ x : chapter14InfiniteIdeleGroup K,
    (∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        hw ((MulEquiv.piUnits x) w : w.Completion)) →
      (chapter14IdeleProductEquiv K).symm (x, 1) ∈ U.subgroup

def chapter14ContainsIntegralUnitTail
    {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) : Prop :=
  ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    ∀ x : chapter14FiniteIdeleGroup K,
      (∀ v ∈ S,
        RestrictedProduct.unitsEquiv _ x v = 1) →
      (∀ v ∉ S,
        RestrictedProduct.unitsEquiv _ x v ∈
          Chapter11.chapter11FiniteLocalUnitGroup K v 0) →
      (chapter14IdeleProductEquiv K).symm (1, x) ∈ U.subgroup

abbrev chapter14IdeleLevelQuotient {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :=
  chapter14IdeleGroup K ⧸
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup)

instance chapter14IdeleLevelQuotientFinite {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    Finite (chapter14IdeleLevelQuotient U) := by
  exact Subgroup.finiteIndex_iff_finite_quotient.mp U.finiteIndex'

def chapter14IdeleLevelQuotientMap {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    chapter14IdeleGroup K →* chapter14IdeleLevelQuotient U :=
  QuotientGroup.mk' _

abbrev chapter14IdeleClassLevelSubgroup {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :=
  Subgroup.map (chapter14IdeleClassMap K)
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup)

instance chapter14IdeleClassLevelSubgroupNormal {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    (chapter14IdeleClassLevelSubgroup U).Normal := by
  exact Subgroup.Normal.map
    (show (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup).Normal from
      { conj_mem := by
          intro n hn g
          simpa using hn })
    (chapter14IdeleClassMap K)
    (by
      simpa [chapter14IdeleClassMap] using
        (QuotientGroup.mk'_surjective (chapter14PrincipalIdeleSubgroup K)))

abbrev chapter14IdeleClassLevelQuotient {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :=
  chapter14IdeleClassGroup K ⧸ chapter14IdeleClassLevelSubgroup U

def chapter14IdeleClassLevelQuotientMap {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    chapter14IdeleClassGroup K →* chapter14IdeleClassLevelQuotient U :=
  QuotientGroup.mk' _

/-- The book-facing class-level quotient and the canonical quotient of ideles agree by the third
isomorphism theorem. -/
def chapter14IdeleClassLevelToIdeleLevelEquiv {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    chapter14IdeleClassLevelQuotient U ≃*
      chapter14IdeleLevelQuotient U :=
  QuotientGroup.quotientQuotientEquivQuotient
    (chapter14PrincipalIdeleSubgroup K)
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup) le_sup_left

theorem chapter14IdeleClassLevelToIdeleLevelEquiv_apply {K : Type*} [Field K]
    [NumberField K] (U : Chapter14FiniteLevel K)
    (x : chapter14IdeleGroup K) :
    chapter14IdeleClassLevelToIdeleLevelEquiv U
        (chapter14IdeleClassLevelQuotientMap U
          (chapter14IdeleClassMap K x)) =
      chapter14IdeleLevelQuotientMap U x := by
  sorry

instance chapter14IdeleClassLevelQuotientFinite {K : Type*} [Field K] [NumberField K]
    (U : Chapter14FiniteLevel K) :
    Finite (chapter14IdeleClassLevelQuotient U) := by
  sorry

/-! Shared archimedean component quotients. -/

def chapter14PositiveRealUnits : Subgroup ℝˣ where
  carrier := {x | (0 : ℝ) < x}
  one_mem' := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  mul_mem' := by
    intro a b ha hb
    change (0 : ℝ) < (a : ℝ) * (b : ℝ)
    exact mul_pos ha hb
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val] using
      (inv_pos.mpr (show (0 : ℝ) < (a : ℝ) from ha))

abbrev chapter14RealSignQuotient := ℝˣ ⧸ chapter14PositiveRealUnits

theorem chapter14_real_sign_quotient_is_finite :
    Finite chapter14RealSignQuotient := by
  sorry

theorem chapter14_real_sign_quotient_has_order_two :
    Nonempty (chapter14RealSignQuotient ≃* Multiplicative (ZMod 2)) := by
  sorry

/-! ## Ray subgroups and ray class quotients -/

abbrev Chapter14Modulus (K : Type*) [Field K] [NumberField K] :=
  Chapter11.RayModulus K

def chapter14ModulusComplexPart {K : Type*} [Field K] [NumberField K]
    (_m : Chapter14Modulus K) : Set (NumberField.InfinitePlace K) :=
  ∅

theorem chapter14ModulusComplexPart_empty {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) : chapter14ModulusComplexPart m = ∅ := rfl

def chapter14RayFiniteLevel {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) : Chapter14FiniteLevel K :=
  { subgroup := Chapter11.chapter11RayUnitSubgroup m
    isOpen' := Chapter11.chapter11_ray_unit_subgroup_is_open m
    finiteIndex' := by
      have hfinite :
          Finite (chapter14IdeleGroup K ⧸
            (chapter14PrincipalIdeleSubgroup K ⊔ Chapter11.chapter11RayUnitSubgroup m)) := by
        rw [chapter14_principal_idele_subgroup_eq_chapter11]
        exact Chapter11.chapter11_ray_class_group_is_finite m
      exact Subgroup.finiteIndex_iff_finite_quotient.mpr hfinite }

abbrev chapter14RayClassGroup {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :=
  chapter14IdeleLevelQuotient (chapter14RayFiniteLevel m)

def chapter14RayClassQuotientMap {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) :
    chapter14IdeleClassGroup K →* chapter14RayClassGroup m :=
  (chapter14IdeleClassLevelToIdeleLevelEquiv (chapter14RayFiniteLevel m)).toMonoidHom.comp
    (chapter14IdeleClassLevelQuotientMap (chapter14RayFiniteLevel m))

/-! ## Absolute values, norms, and the knot group -/

/-! The module and norm-one class group are the canonical Chapter 9 constructions. -/
abbrev chapter14ClassModule (K : Type*) [Field K] [NumberField K] :=
  Chapter09.chapter09IdeleClassModule K

abbrev chapter14NormOneClassSubgroup (K : Type*) [Field K] [NumberField K] :=
  Chapter09.chapter09ClassNormOne K

abbrev chapter14FieldNormOnUnits (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Chapter10.chapter10LocalNormUnitHom K L

/-! Chapter 10 supplies generic local norm and continuity interfaces; this record supplies the
number-field-wide idele norm and local-global norm predicate needed by this chapter.  No
surjectivity is assumed here. -/
structure Chapter14AdelicNormInterface (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] where
  ideleNorm : chapter14IdeleGroup L →* chapter14IdeleGroup K
  ideleNorm_continuous : Continuous ideleNorm
  galoisRestriction : chapter14AbelianGaloisGroup L →*
    chapter14AbelianGaloisGroup K
  map_principal :
    ∀ {x : chapter14IdeleGroup L},
      x ∈ chapter14PrincipalIdeleSubgroup L →
        ideleNorm x ∈ chapter14PrincipalIdeleSubgroup K
  fieldNorm_principal :
    ∀ x : Lˣ,
      ideleNorm (chapter14PrincipalIdeleEmbedding L x) =
        chapter14PrincipalIdeleEmbedding K (chapter14FieldNormOnUnits K L x)
  module_compatibility :
    ∀ y : chapter14IdeleGroup L,
      Chapter09.chapter09IdeleModuleHom K (ideleNorm y) =
        Chapter09.chapter09IdeleModuleHom L y
  localNormAtEveryPlace : Kˣ → Prop
  localNorm_one : localNormAtEveryPlace 1
  localNorm_mul : ∀ {x y : Kˣ}, localNormAtEveryPlace x →
    localNormAtEveryPlace y → localNormAtEveryPlace (x * y)
  localNorm_inv : ∀ {x : Kˣ}, localNormAtEveryPlace x →
    localNormAtEveryPlace x⁻¹
  localNorm_iff_idele :
    ∀ x : Kˣ, localNormAtEveryPlace x ↔
      ∃ y : chapter14IdeleGroup L,
        ideleNorm y = chapter14PrincipalIdeleEmbedding K x

def chapter14NormOnClassGroups {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14IdeleClassGroup L →* chapter14IdeleClassGroup K :=
  QuotientGroup.lift (chapter14PrincipalIdeleSubgroup L)
    ((chapter14IdeleClassMap K).comp N.ideleNorm) (by
      intro x hx
      exact (QuotientGroup.eq_one_iff _).2 (N.map_principal hx))

def chapter14ClassNormSubgroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    Subgroup (chapter14IdeleClassGroup K) :=
  (chapter14NormOnClassGroups N).range

@[simp]
theorem chapter14NormOnClassGroups_apply {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) (y : chapter14IdeleGroup L) :
    chapter14NormOnClassGroups N (chapter14IdeleClassMap L y) =
      chapter14IdeleClassMap K (N.ideleNorm y) := by
  rfl

def chapter14GlobalNormSubgroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (_N : Chapter14AdelicNormInterface K L) : Subgroup Kˣ :=
  (chapter14FieldNormOnUnits K L).range

def chapter14EverywhereLocalNormSubgroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) : Subgroup Kˣ where
  carrier := {x | N.localNormAtEveryPlace x}
  one_mem' := N.localNorm_one
  mul_mem' := by
    intro x y hx hy
    exact N.localNorm_mul hx hy
  inv_mem' := by
    intro x hx
    exact N.localNorm_inv hx

theorem chapter14GlobalNormSubgroup_le_local {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14GlobalNormSubgroup N ≤ chapter14EverywhereLocalNormSubgroup N := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change N.localNormAtEveryPlace (chapter14FieldNormOnUnits K L y)
  exact (N.localNorm_iff_idele (chapter14FieldNormOnUnits K L y)).mpr
    ⟨chapter14PrincipalIdeleEmbedding L y, N.fieldNorm_principal y⟩

abbrev chapter14KnotGroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :=
  chapter14EverywhereLocalNormSubgroup N ⧸
    (chapter14GlobalNormSubgroup N).subgroupOf
      (chapter14EverywhereLocalNormSubgroup N)

theorem chapter14KnotGroup_eq_one_iff {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (x : chapter14EverywhereLocalNormSubgroup N) :
    (QuotientGroup.mk x : chapter14KnotGroup N) = 1 ↔
      (x : Kˣ) ∈ chapter14GlobalNormSubgroup N := by
  constructor
  · intro hx
    exact Subgroup.mem_subgroupOf.mp <|
      (QuotientGroup.eq_one_iff
        (N := (chapter14GlobalNormSubgroup N).subgroupOf
          (chapter14EverywhereLocalNormSubgroup N)) x).mp hx
  · intro hx
    apply (QuotientGroup.eq_one_iff
      (N := (chapter14GlobalNormSubgroup N).subgroupOf
        (chapter14EverywhereLocalNormSubgroup N)) x).mpr
    exact Subgroup.mem_subgroupOf.mpr hx

end LastLib.Book04AdelesAndIdeles.Chapter14
