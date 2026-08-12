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
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K

abbrev chapter14AdeleRing (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (NumberField.RingOfIntegers K) K

abbrev chapter14FiniteIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (chapter14FiniteAdeleRing K)ˣ

abbrev chapter14InfiniteIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (NumberField.InfiniteAdeleRing K)ˣ

abbrev chapter14IdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (chapter14AdeleRing K)ˣ

abbrev chapter14IdealClassGroup (K : Type*) [Field K] [NumberField K] :=
  ClassGroup (NumberField.RingOfIntegers K)

/-- The product decomposition of an idele into its infinite and finite parts. -/
def chapter14IdeleProductEquiv (K : Type*) [Field K] [NumberField K] :
    chapter14IdeleGroup K ≃*
      chapter14InfiniteIdeleGroup K × chapter14FiniteIdeleGroup K :=
  MulEquiv.prodUnits

theorem chapter14_finite_idele_integral_tail {K : Type*} [Field K] [NumberField K]
    (a : chapter14FiniteIdeleGroup K) :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
      in Filter.cofinite,
      Valued.v (RestrictedProduct.unitsEquiv _ a v).1 = 1 := by
  exact IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a

/-- Principal ideles are the units obtained from the diagonal field embedding. -/
def chapter14PrincipalIdeleEmbedding (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter14IdeleGroup K :=
  Units.map (algebraMap K (chapter14AdeleRing K)).toMonoidHom

abbrev chapter14PrincipalIdeleSubgroup (K : Type*) [Field K] [NumberField K] :=
  (chapter14PrincipalIdeleEmbedding K).range

abbrev chapter14IdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  chapter14IdeleGroup K ⧸ chapter14PrincipalIdeleSubgroup K

def chapter14IdeleClassMap (K : Type*) [Field K] [NumberField K] :
    chapter14IdeleGroup K →* chapter14IdeleClassGroup K :=
  QuotientGroup.mk' _

@[simp]
theorem chapter14IdeleClassMap_apply (K : Type*) [Field K] [NumberField K]
    (x : chapter14IdeleGroup K) :
    chapter14IdeleClassMap K x = QuotientGroup.mk x := rfl

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

/-!
The next structures are local dependency interfaces.  The preceding chapters of the book are not
yet available as stable LastLib declarations in this drafting pass, so these fields isolate exactly
which local embeddings, open subgroups, and unit tails the chapter uses.
-/

/- LOCAL_DEPENDENCY_GUESS: the local-to-global embedding maps are supplied by the earlier adelic
chapters in the reconciled library. -/
structure Chapter14LocalComponentData (K : Type*) [Field K] [NumberField K] where
  finiteComponent : ∀ v : NumberField.FinitePlace K,
    (v.maximalIdeal.adicCompletion K)ˣ →* chapter14IdeleGroup K
  infiniteComponent : ∀ w : NumberField.InfinitePlace K,
    (w.Completion)ˣ →* chapter14IdeleGroup K

/- LOCAL_DEPENDENCY_GUESS: these subgroups package the positive archimedean directions and the
integral-unit restricted-product tail used by the finite-level statements. -/
structure Chapter14IdeleLevelData (K : Type*) [Field K] [NumberField K]
    extends Chapter14LocalComponentData K where
  positiveMagnitudeDirections : Subgroup (chapter14IdeleGroup K)
  integralUnitTail : NumberField.FinitePlace K → Subgroup (chapter14IdeleGroup K)

structure Chapter14FiniteLevel {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) where
  subgroup : Subgroup (chapter14IdeleGroup K)
  isOpen' : IsOpen (subgroup : Set (chapter14IdeleGroup K))
  containsPositiveMagnitudeDirections : D.positiveMagnitudeDirections ≤ subgroup
  containsIntegralTail :
    ∀ᶠ v : NumberField.FinitePlace K in Filter.cofinite,
      D.integralUnitTail v ≤ subgroup
  finiteIndex' :
    (chapter14PrincipalIdeleSubgroup K ⊔ subgroup).FiniteIndex

abbrev chapter14IdeleLevelQuotient {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :=
  chapter14IdeleGroup K ⧸
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup)

instance chapter14IdeleLevelQuotientFinite {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    Finite (chapter14IdeleLevelQuotient D U) := by
  exact Subgroup.finiteIndex_iff_finite_quotient.mp U.finiteIndex'

def chapter14IdeleLevelQuotientMap {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    chapter14IdeleGroup K →* chapter14IdeleLevelQuotient D U :=
  QuotientGroup.mk' _

abbrev chapter14IdeleClassLevelSubgroup {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :=
  Subgroup.map (chapter14IdeleClassMap K)
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup)

instance chapter14IdeleClassLevelSubgroupNormal {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    (chapter14IdeleClassLevelSubgroup D U).Normal := by
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
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :=
  chapter14IdeleClassGroup K ⧸ chapter14IdeleClassLevelSubgroup D U

def chapter14IdeleClassLevelQuotientMap {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    chapter14IdeleClassGroup K →* chapter14IdeleClassLevelQuotient D U :=
  QuotientGroup.mk' _

/-- The book-facing class-level quotient and the canonical quotient of ideles agree by the third
isomorphism theorem. -/
def chapter14IdeleClassLevelToIdeleLevelEquiv {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    chapter14IdeleClassLevelQuotient D U ≃*
      chapter14IdeleLevelQuotient D U :=
  QuotientGroup.quotientQuotientEquivQuotient
    (chapter14PrincipalIdeleSubgroup K)
    (chapter14PrincipalIdeleSubgroup K ⊔ U.subgroup) le_sup_left

theorem chapter14IdeleClassLevelToIdeleLevelEquiv_apply {K : Type*} [Field K]
    [NumberField K] (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D)
    (x : chapter14IdeleGroup K) :
    chapter14IdeleClassLevelToIdeleLevelEquiv D U
        (chapter14IdeleClassLevelQuotientMap D U
          (chapter14IdeleClassMap K x)) =
      chapter14IdeleLevelQuotientMap D U x := by
  sorry

instance chapter14IdeleClassLevelQuotientFinite {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (U : Chapter14FiniteLevel D) :
    Finite (chapter14IdeleClassLevelQuotient D U) := by
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
    Nonempty (chapter14RealSignQuotient ≃* ZMod 2) := by
  sorry

def chapter14ComplexMagnitudeSubgroup : Subgroup ℂˣ := ⊤

abbrev chapter14ComplexMagnitudeQuotient :=
  ℂˣ ⧸ chapter14ComplexMagnitudeSubgroup

theorem chapter14_complex_place_has_no_finite_sign_quotient :
    Subsingleton chapter14ComplexMagnitudeQuotient := by
  sorry

/-! ## Ray subgroups and ray class quotients -/

structure Chapter14Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : Ideal (NumberField.RingOfIntegers K)
  finitePart_ne_bot : finitePart ≠ ⊥
  realPart : Set (NumberField.InfinitePlace K)
  realPart_isReal : realPart ⊆ {w | NumberField.InfinitePlace.IsReal w}

def chapter14ModulusComplexPart {K : Type*} [Field K] [NumberField K]
    (_m : Chapter14Modulus K) : Set (NumberField.InfinitePlace K) :=
  ∅

theorem chapter14ModulusComplexPart_empty {K : Type*} [Field K] [NumberField K]
    (m : Chapter14Modulus K) : chapter14ModulusComplexPart m = ∅ := rfl

/- LOCAL_DEPENDENCY_GUESS: the ray subgroup is supplied by the earlier ray-class construction;
the fields state precisely the openness, tail, finite-index, and cofinality facts needed here. -/
structure Chapter14RaySubgroupFamily {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) where
  raySubgroup : Chapter14Modulus K → Subgroup (chapter14IdeleGroup K)
  raySubgroup_open : ∀ m, IsOpen (raySubgroup m : Set (chapter14IdeleGroup K))
  raySubgroup_containsPositive :
    ∀ m, D.positiveMagnitudeDirections ≤ raySubgroup m
  raySubgroup_containsIntegralTail :
    ∀ m, ∀ᶠ v : NumberField.FinitePlace K in Filter.cofinite,
      D.integralUnitTail v ≤ raySubgroup m
  raySubgroup_finiteIndex :
    ∀ m, (chapter14PrincipalIdeleSubgroup K ⊔ raySubgroup m).FiniteIndex
  ray_subgroup_cofinal :
    ∀ U : Chapter14FiniteLevel D, ∃ m, raySubgroup m ≤ U.subgroup

def chapter14RayFiniteLevel {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) : Chapter14FiniteLevel D :=
  { subgroup := R.raySubgroup m
    isOpen' := R.raySubgroup_open m
    containsPositiveMagnitudeDirections := R.raySubgroup_containsPositive m
    containsIntegralTail := R.raySubgroup_containsIntegralTail m
    finiteIndex' := R.raySubgroup_finiteIndex m }

abbrev chapter14RayClassGroup {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) :=
  chapter14IdeleClassLevelQuotient D (chapter14RayFiniteLevel D R m)

def chapter14RayClassQuotientMap {K : Type*} [Field K] [NumberField K]
    (D : Chapter14IdeleLevelData K) (R : Chapter14RaySubgroupFamily D)
    (m : Chapter14Modulus K) :
    chapter14IdeleClassGroup K →* chapter14RayClassGroup D R m :=
  chapter14IdeleClassLevelQuotientMap D (chapter14RayFiniteLevel D R m)

/-! ## Absolute values, norms, and the knot group -/

structure Chapter14ModuleData (K : Type*) [Field K] [NumberField K] where
  module : chapter14IdeleGroup K →* ℝ≥0ˣ
  principal_one :
    ∀ x : Kˣ, module (chapter14PrincipalIdeleEmbedding K x) = 1

def chapter14ClassModule {K : Type*} [Field K] [NumberField K]
    (M : Chapter14ModuleData K) : chapter14IdeleClassGroup K →* ℝ≥0ˣ :=
  QuotientGroup.lift (chapter14PrincipalIdeleSubgroup K) M.module (by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    exact M.principal_one y)

def chapter14NormOneClassSubgroup {K : Type*} [Field K] [NumberField K]
    (M : Chapter14ModuleData K) : Subgroup (chapter14IdeleClassGroup K) where
  carrier := {x | chapter14ClassModule M x = 1}
  one_mem' := by
    change chapter14ClassModule M (1 : chapter14IdeleClassGroup K) = 1
    exact map_one (chapter14ClassModule M)
  mul_mem' := by
    intro a b ha hb
    change chapter14ClassModule M (a * b) = 1
    rw [map_mul, ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    change chapter14ClassModule M a⁻¹ = 1
    rw [map_inv, ha, inv_one]

def chapter14FieldNormOnUnits (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/- LOCAL_DEPENDENCY_GUESS: local norm groups and the adelic norm map are the interfaces supplied by
the norm/functoriality chapters.  No surjectivity is assumed here. -/
structure Chapter14AdelicNormInterface (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] where
  ideleNorm : chapter14IdeleGroup L →* chapter14IdeleGroup K
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
  moduleK : Chapter14ModuleData K
  moduleL : Chapter14ModuleData L
  module_compatibility :
    ∀ y : chapter14IdeleGroup L, moduleK.module (ideleNorm y) = moduleL.module y
  localNormAtEveryPlace : Kˣ → Prop
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
  one_mem' := by sorry
  mul_mem' := by sorry
  inv_mem' := by sorry

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
