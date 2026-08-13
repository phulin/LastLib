import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import LastLib.Book04AdelesAndIdeles.Chapter08.Section81

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open scoped BigOperators NNReal NumberField.AdeleRing RestrictedProduct

open NumberField IsDedekindDomain

/-!
## Shared interfaces for Chapter 9

Mathlib supplies the finite and infinite adele rings, their restricted-product
unit descriptions, the normalized local absolute values, the number-field
product formula, the ideal class group, and Dirichlet's unit lattice.  The
preceding book chapters are not present in this checkout, so this file records
only the small book-facing bridges needed by the idele-module chapter.
-/

abbrev Chapter09RingOfIntegers (K : Type*) [Field K] [NumberField K] := 𝓞 K

abbrev Chapter09FiniteAdele (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev Chapter09InfiniteAdele (K : Type*) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K

abbrev Chapter09Adele (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

/-! The ambient adele and each nonarchimedean completion use their Borel
measurable structure for the measure-theoretic statements in Section 9.7. -/

noncomputable instance chapter09AdeleMeasurableSpace
    (K : Type*) [Field K] [NumberField K] :
    MeasurableSpace (Chapter09Adele K) :=
  borel _

noncomputable instance chapter09AdicCompletionMeasurableSpace
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) :=
  borel _

noncomputable instance chapter09AdeleBorelSpace
    (K : Type*) [Field K] [NumberField K] :
    BorelSpace (Chapter09Adele K) :=
  ⟨rfl⟩

noncomputable instance chapter09AdicCompletionBorelSpace
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) :=
  ⟨rfl⟩

/-- Ideles are the units of the full adele ring. -/
abbrev Chapter09Idele (K : Type*) [Field K] [NumberField K] :=
  (Chapter09Adele K)ˣ

/-- The positive real multiplicative group, represented canonically by units of `ℝ≥0`. -/
abbrev Chapter09PositiveReal : Type := ℝ≥0ˣ

/-- Ideal class groups are used with their discrete topology in the finite-image
statements of this chapter. -/
noncomputable instance chapter09ClassGroupTopologicalSpace
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (ClassGroup (𝓞 K)) := ⊥

noncomputable instance chapter09ClassGroupDiscreteTopology
    (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (ClassGroup (𝓞 K)) where
  eq_bot := rfl

/-- The canonical product decomposition of a full idele into its infinite and finite parts. -/
def chapter09IdeleProductEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K ≃* (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ :=
  MulEquiv.prodUnits

/-- The product decomposition also respects the unit-group topologies. -/
def chapter09IdeleProductContinuousEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K ≃ₜ*
      (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ where
  __ := chapter09IdeleProductEquiv K
  continuous_toFun :=
    (Homeomorph.prodUnits :
      (Chapter09Adele K)ˣ ≃ₜ
        (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ).continuous
  continuous_invFun :=
    (Homeomorph.prodUnits :
      (Chapter09Adele K)ˣ ≃ₜ
        (Chapter09InfiniteAdele K)ˣ × (Chapter09FiniteAdele K)ˣ).symm.continuous

/-! ### Local absolute-value factors -/

/-- Package the norm of a local unit as a positive real. -/
def chapter09NormUnit {F : Type*} [NormedField F] (u : Fˣ) : Chapter09PositiveReal :=
  Units.mk0 ‖(u : F)‖₊ (by simp [Units.ne_zero u])

@[simp]
theorem chapter09NormUnit_coe {F : Type*} [NormedField F] (u : Fˣ) :
    ((chapter09NormUnit u : Chapter09PositiveReal) : ℝ≥0) = ‖(u : F)‖₊ := by
  rfl

theorem chapter09NormUnit_pos {F : Type*} [NormedField F] (u : Fˣ) :
    ((chapter09NormUnit u : Chapter09PositiveReal) : ℝ≥0) ≠ 0 := by
  exact Units.ne_zero _

def chapter09NormUnitHom {F : Type*} [NormedField F] :
    Fˣ →* Chapter09PositiveReal where
  toFun := chapter09NormUnit
  map_one' := by
    ext
    simp [chapter09NormUnit]
  map_mul' u v := by
    ext
    simp [chapter09NormUnit, nnnorm_mul]

@[simp]
theorem chapter09NormUnitHom_apply {F : Type*} [NormedField F] (u : Fˣ) :
    chapter09NormUnitHom u = chapter09NormUnit u :=
  rfl

/-! Mathlib's norm on a finite adic completion is `exp (-ord)`, whereas the
book's normalized finite-place absolute value is `q_v ^ (-ord)`.  Keep the
finite normalization separate from `chapter09NormUnit`, which is used for the
archimedean factors. -/
def chapter09FiniteNormUnit
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) : Chapter09PositiveReal :=
  Units.mk0
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        (u : v.adicCompletion K))) (by sorry)

@[simp]
theorem chapter09FiniteNormUnit_coe
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ((chapter09FiniteNormUnit v u : Chapter09PositiveReal) : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^
        (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (u : v.adicCompletion K)) :=
  rfl

/-! ### Finite, infinite, and full idele modules -/

def chapter09FiniteIdeleModule
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09FiniteAdele K)ˣ) : Chapter09PositiveReal :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    chapter09FiniteNormUnit v
      ((RestrictedProduct.unitsEquiv
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v)

def chapter09InfiniteIdeleModule
    {K : Type*} [Field K] [NumberField K]
    (x : (Chapter09InfiniteAdele K)ˣ) : Chapter09PositiveReal :=
  ∏ v : InfinitePlace K,
    (chapter09NormUnit ((MulEquiv.piUnits x) v)) ^ v.mult

def chapter09IdeleModule
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09Idele K) : Chapter09PositiveReal :=
  chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K x).1) *
    chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K x).2)

theorem chapter09IdeleModule_eq_infinite_mul_finite
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleModule x =
      chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K x).1) *
        chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K x).2) :=
  rfl

/- The finiteness of the restricted product is the only nontrivial input in
the multiplicativity proof below; it is deliberately kept separate from the
definition so later sections can use it as an API lemma. -/
def chapter09IdeleModuleHom
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K →* Chapter09PositiveReal where
  toFun := chapter09IdeleModule
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

@[simp]
theorem chapter09IdeleModuleHom_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleModuleHom K x = chapter09IdeleModule x :=
  rfl

theorem chapter09IdeleModule_ne_zero
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    ((chapter09IdeleModule x : Chapter09PositiveReal) : ℝ≥0) ≠ 0 := by
  exact Units.ne_zero _

theorem chapter09FiniteIdeleModule_ne_zero
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09FiniteAdele K)ˣ) :
    ((chapter09FiniteIdeleModule x : Chapter09PositiveReal) : ℝ≥0) ≠ 0 := by
  exact Units.ne_zero _

theorem chapter09InfiniteIdeleModule_ne_zero
    {K : Type*} [Field K] [NumberField K] (x : (Chapter09InfiniteAdele K)ˣ) :
    ((chapter09InfiniteIdeleModule x : Chapter09PositiveReal) : ℝ≥0) ≠ 0 := by
  exact Units.ne_zero _

def chapter09FiniteIdelePartHom
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K →* (Chapter09FiniteAdele K)ˣ where
  toFun x := (chapter09IdeleProductEquiv K x).2
  map_one' := by sorry
  map_mul' x y := by sorry

@[simp]
theorem chapter09FiniteIdelePartHom_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09FiniteIdelePartHom K x = (chapter09IdeleProductEquiv K x).2 :=
  rfl

/-! ### Principal ideles and class groups -/

/-- The diagonal embedding of nonzero global elements into the ideles. -/
def chapter09PrincipalIdele
    (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter09Idele K :=
  Units.map (algebraMap K (Chapter09Adele K))

def chapter09PrincipalIdeleSubgroup
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  (chapter09PrincipalIdele K).range

def chapter09FinitePrincipalIdele
    (K : Type*) [Field K] [NumberField K] :
    Kˣ →* (Chapter09FiniteAdele K)ˣ :=
  (chapter09FiniteIdelePartHom K).comp (chapter09PrincipalIdele K)

def chapter09FiniteUnitIdeles
    (K : Type*) [Field K] [NumberField K] :
  Subgroup (Chapter09FiniteAdele K)ˣ :=
  LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits (K := K)

/-!
`Chapter09IdeleIdealData` is the one boundary with Chapter 8.  It records the
finite-idele-to-ideal-class interface needed below: functoriality, triviality
on principal ideles, representation of every ideal class, and the kernel
description by principal finite ideles and finite unit ideles.  It contains no
compactness conclusion.  The canonical number-field instance below is built
from the preceding chapter's valuation-to-ideal map.
-/

/- LOCAL_DEPENDENCY_BRIDGE: keep the preceding chapter's ideal construction
behind this small class-valued interface until it is available here. -/
structure Chapter09IdeleIdealData
    (K : Type*) [Field K] [NumberField K] where
  idealClassMap : (Chapter09FiniteAdele K)ˣ →* ClassGroup (𝓞 K)
  principal_is_trivial :
    ∀ a : Kˣ,
      idealClassMap (chapter09FinitePrincipalIdele K a) = 1
  kernel_eq_principal_mul_units :
    idealClassMap.ker =
      (chapter09FinitePrincipalIdele K).range ⊔ chapter09FiniteUnitIdeles K
  surjective : Function.Surjective idealClassMap

/-! The preceding chapter already constructs the valuation-vector-to-ideal map.
The generic structure above remains useful as a small book-facing interface,
but the number-field specialization used by the unconditional compactness
statements below must be tied to that canonical construction rather than left
as an uninstantiated parameter. -/

noncomputable def chapter09CanonicalIdeleIdealData
    (K : Type*) [Field K] [NumberField K] : Chapter09IdeleIdealData K where
  idealClassMap :=
    (ClassGroup.mk K).comp
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K)
  principal_is_trivial := by
    sorry
  kernel_eq_principal_mul_units := by
    sorry
  surjective := by
    sorry

theorem chapter09FiniteUnitIdeles_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {x : (Chapter09FiniteAdele K)ˣ} :
    x ∈ chapter09FiniteUnitIdeles K ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        chapter09FiniteNormUnit v
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) = 1 := by
  sorry

abbrev Chapter09IdeleClassGroup
    (K : Type*) [Field K] [NumberField K] :=
  Chapter09Idele K ⧸ chapter09PrincipalIdeleSubgroup K

def chapter09NormOneIdeles
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  (chapter09IdeleModuleHom K).ker

theorem chapter09NormOneIdeles_mem_iff
    {K : Type*} [Field K] [NumberField K] {x : Chapter09Idele K} :
    x ∈ chapter09NormOneIdeles K ↔ chapter09IdeleModuleHom K x = 1 := by
  rfl

theorem chapter09PrincipalIdele_module_eq_one
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    chapter09IdeleModule (chapter09PrincipalIdele K a) = 1 := by
  sorry

theorem chapter09PrincipalIdele_degree_eq_zero
    {K : Type*} [Field K] [NumberField K] (a : Kˣ) :
    -Real.log (((chapter09IdeleModule (chapter09PrincipalIdele K a) :
      Chapter09PositiveReal) : ℝ≥0) : ℝ) = 0 := by
  rw [chapter09PrincipalIdele_module_eq_one]
  simp

def chapter09NormOnePrincipalIdele
    (K : Type*) [Field K] [NumberField K] :
    Kˣ →* chapter09NormOneIdeles K where
  toFun a := ⟨chapter09PrincipalIdele K a, by
    sorry⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp

abbrev Chapter09NormOneClassGroup
    (K : Type*) [Field K] [NumberField K] :=
  chapter09NormOneIdeles K ⧸ (chapter09NormOnePrincipalIdele K).range

def chapter09IdeleClassModule
    (K : Type*) [Field K] [NumberField K] :
    Chapter09IdeleClassGroup K →* Chapter09PositiveReal :=
  QuotientGroup.lift (chapter09PrincipalIdeleSubgroup K)
    (chapter09IdeleModuleHom K) (by
      intro x hx
      sorry)

theorem chapter09IdeleClassModule_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleClassModule K (QuotientGroup.mk x) =
      chapter09IdeleModuleHom K x := by
  rfl

def chapter09ClassNormOne
    (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter09IdeleClassGroup K) :=
  (chapter09IdeleClassModule K).ker

theorem chapter09ClassNormOne_mem_iff
    {K : Type*} [Field K] [NumberField K] {x : Chapter09IdeleClassGroup K} :
    x ∈ chapter09ClassNormOne K ↔ chapter09IdeleClassModule K x = 1 := by
  rfl

/-! ### The ideal-class map on the idele class group -/

def chapter09IdeleClassIdealClassMap
    (K : Type*) [Field K] [NumberField K] :
    Chapter09IdeleClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (chapter09PrincipalIdeleSubgroup K)
    ((chapter09CanonicalIdeleIdealData K).idealClassMap.comp
      (chapter09FiniteIdelePartHom K)) (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      simpa [chapter09FinitePrincipalIdele] using
        (chapter09CanonicalIdeleIdealData K).principal_is_trivial a)

@[simp]
theorem chapter09IdeleClassIdealClassMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter09Idele K) :
    chapter09IdeleClassIdealClassMap K (QuotientGroup.mk x) =
      (chapter09CanonicalIdeleIdealData K).idealClassMap
        (chapter09FiniteIdelePartHom K x) := by
  rfl

def chapter09NormOneClassIdealClassMap
    (K : Type*) [Field K] [NumberField K] :
    chapter09ClassNormOne K →* ClassGroup (𝓞 K) :=
  (chapter09IdeleClassIdealClassMap K).comp (chapter09ClassNormOne K).subtype

theorem chapter09NormOneClassIdealClassMap_apply
    {K : Type*} [Field K] [NumberField K]
    (x : chapter09ClassNormOne K) :
    chapter09NormOneClassIdealClassMap K x =
      chapter09IdeleClassIdealClassMap K x.1 :=
  rfl

noncomputable def chapter09NormOneClassGroup_equiv_classNormOne
    {K : Type*} [Field K] [NumberField K] :
    Chapter09NormOneClassGroup K ≃* chapter09ClassNormOne K := by
  sorry

/-! The compactness arguments use the quotient topology on both sides, so the
algebraic identification above also needs its topological form. -/
noncomputable def chapter09NormOneClassGroup_continuousEquiv_classNormOne
    {K : Type*} [Field K] [NumberField K] :
    Chapter09NormOneClassGroup K ≃ₜ* chapter09ClassNormOne K := by
  sorry

/-! ### Finite unit ideles and the archimedean norm-one subgroup -/

def chapter09FiniteUnitIdeleEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09FiniteAdele K)ˣ →* Chapter09Idele K where
  toFun u :=
    (chapter09IdeleProductEquiv K).symm (1, u)
  map_one' := by sorry
  map_mul' x y := by sorry

def chapter09FiniteUnitIdeleSubgroup
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  Subgroup.map (chapter09FiniteUnitIdeleEmbedding K)
    (chapter09FiniteUnitIdeles K)

def chapter09PrincipalTimesFiniteUnits
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  chapter09PrincipalIdeleSubgroup K ⊔ chapter09FiniteUnitIdeleSubgroup K

def chapter09InfiniteIdeleModuleHom
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09InfiniteAdele K)ˣ →* Chapter09PositiveReal where
  toFun := chapter09InfiniteIdeleModule
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

def chapter09KInfinityOne
    (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter09InfiniteAdele K)ˣ :=
  (chapter09InfiniteIdeleModuleHom K).ker

theorem chapter09KInfinityOne_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {x : (Chapter09InfiniteAdele K)ˣ} :
    x ∈ chapter09KInfinityOne K ↔ chapter09InfiniteIdeleModuleHom K x = 1 := by
  rfl

def chapter09InfiniteUnitEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* (Chapter09InfiniteAdele K)ˣ :=
  Units.map ((algebraMap K (Chapter09InfiniteAdele K)).comp
    (algebraMap (𝓞 K) K))

def chapter09FiniteUnitEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* (Chapter09FiniteAdele K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitEmbedding (𝓞 K) K).comp
    (Units.map (algebraMap (𝓞 K) K))

def chapter09ArchimedeanUnitEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* chapter09KInfinityOne K where
  toFun u := ⟨chapter09InfiniteUnitEmbedding K u, by
    sorry⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

def chapter09FiniteUnitSubtypeEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* chapter09FiniteUnitIdeles K where
  toFun u := ⟨chapter09FiniteUnitEmbedding K u, by
    sorry⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

abbrev Chapter09ArchFiniteUnitNumerator
    (K : Type*) [Field K] [NumberField K] :=
  chapter09KInfinityOne K × chapter09FiniteUnitIdeles K

def chapter09GlobalUnitDiagonal
    (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* Chapter09ArchFiniteUnitNumerator K where
  toFun u :=
    (chapter09ArchimedeanUnitEmbedding K u,
      chapter09FiniteUnitSubtypeEmbedding K u)
  map_one' := by
    ext <;> simp
  map_mul' u v := by
    ext <;> simp

abbrev Chapter09ArchFiniteUnitKernel
    (K : Type*) [Field K] [NumberField K] :=
  Chapter09ArchFiniteUnitNumerator K ⧸ (chapter09GlobalUnitDiagonal K).range

def chapter09ArchFiniteToNormOneIdele
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchFiniteUnitNumerator K →* chapter09NormOneIdeles K where
  toFun x := ⟨
    (chapter09IdeleProductEquiv K).symm
      (x.1.1, x.2.1), by
      sorry⟩
  map_one' := by sorry
  map_mul' x y := by sorry

def chapter09ArchFiniteToNormOneClassGroup
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchFiniteUnitKernel K →* Chapter09NormOneClassGroup K :=
  QuotientGroup.lift (chapter09GlobalUnitDiagonal K).range
    ((QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range).comp
      (chapter09ArchFiniteToNormOneIdele K)) (by
      intro x hx
      rcases hx with ⟨u, rfl⟩
      sorry)

/-! ### Exact-sequence and topological bookkeeping -/

structure Chapter09ShortExactGroup
    (A B C : Type*) [Group A] [Group B] [Group C] where
  left : A →* B
  right : B →* C
  left_injective : Function.Injective left
  exact : Function.MulExact left right
  right_surjective : Function.Surjective right

theorem chapter09NormOneIdeles_is_normal
    (K : Type*) [Field K] [NumberField K] :
    (chapter09NormOneIdeles K).Normal := by
  infer_instance

theorem chapter09FiniteUnitIdeleSubgroup_is_normal
    (K : Type*) [Field K] [NumberField K] :
    (chapter09FiniteUnitIdeleSubgroup K).Normal := by
  infer_instance

theorem chapter09PrincipalTimesFiniteUnits_is_normal
    (K : Type*) [Field K] [NumberField K] :
    (chapter09PrincipalTimesFiniteUnits K).Normal := by
  infer_instance

end

end LastLib.Book04AdelesAndIdeles.Chapter09
