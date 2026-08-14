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
import LastLib.Book04AdelesAndIdeles.Chapter08.Section87

namespace LastLib.Book04AdelesAndIdeles.Chapter09

noncomputable section

open Topology
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

/-! ### Locally compact adele interfaces -/

/- The finite-adic restricted product is locally compact once its local
completion fields and the integral subgroups are supplied with their standard
compactness data.  These declarations keep that prerequisite chain available
to the full-adele and Haar-character APIs. -/
theorem chapter09_adic_completion_locally_compact
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := by
  sorry

theorem chapter09_adic_completion_integers_compact
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  sorry

theorem chapter09_finite_adele_integral_subgroups_compact
    (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  sorry

theorem chapter09_finite_adele_locally_compact
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter09FiniteAdele K) := by
  sorry

noncomputable instance chapter09FiniteAdeleLocallyCompactSpace
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter09FiniteAdele K) :=
  chapter09_finite_adele_locally_compact K

theorem chapter09_adele_locally_compact
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter09Adele K) := by
  sorry

noncomputable instance chapter09AdeleLocallyCompactSpace
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter09Adele K) :=
  chapter09_adele_locally_compact K

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
        (u : v.adicCompletion K))) (by
          exact zpow_ne_zero _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v))

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
    have hone : chapter09IdeleProductEquiv K (1 : Chapter09Idele K) = (1, 1) :=
      (chapter09IdeleProductEquiv K).map_one
    have hinf : chapter09InfiniteIdeleModule (1 : (Chapter09InfiniteAdele K)ˣ) = 1 := by
      unfold chapter09InfiniteIdeleModule
      have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
        (MulEquiv.piUnits).map_one
      rw [hpi]
      simp [chapter09NormUnit]
    have hfin : chapter09FiniteIdeleModule (1 : (Chapter09FiniteAdele K)ˣ) = 1 := by
      unfold chapter09FiniteIdeleModule
      have hunits : RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
          (1 : (Chapter09FiniteAdele K)ˣ) = 1 :=
        (RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)).map_one
      rw [hunits]
      have horder : ∀ v : HeightOneSpectrum (𝓞 K),
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
            (1 : v.adicCompletion K) = 0 := by
        intro v
        have hone0 : (1 : v.adicCompletion K) ≠ 0 := one_ne_zero
        apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
          v (1 : v.adicCompletion K) hone0).2
        exact Valuation.map_one _
      have hfactor : ∀ v : HeightOneSpectrum (𝓞 K),
          chapter09FiniteNormUnit v
            ((1 : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) v) = 1 := by
        intro v
        apply Units.ext
        change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
          (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
            (↑((1 : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) v) :
              v.adicCompletion K)) = 1
        have hv : (↑((1 : ∀ v : HeightOneSpectrum (𝓞 K),
            (v.adicCompletion K)ˣ) v) : v.adicCompletion K) = 1 := by
          rfl
        rw [hv, horder v]
        simp
      apply finprod_eq_one_of_forall_eq_one
      intro v
      exact hfactor v
    change chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K
      (1 : Chapter09Idele K)).1) *
      chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K
        (1 : Chapter09Idele K)).2) = 1
    rw [hone]
    simp [hinf, hfin]
  map_mul' x y := by
    classical
    let U := RestrictedProduct.unitsEquiv
      (𝓕 := Filter.cofinite)
      (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    have hsupport : ∀ z : (Chapter09FiniteAdele K)ˣ,
        Function.HasFiniteMulSupport
          (fun v : HeightOneSpectrum (𝓞 K) =>
            chapter09FiniteNormUnit v (U z v)) := by
      intro z
      rw [Function.HasFiniteMulSupport]
      apply Filter.eventually_cofinite.mp
      filter_upwards [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_order_eventually_eq_zero z]
        with v hv
      apply Units.ext
      change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
        (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (↑(U z v) : v.adicCompletion K)) = 1
      have heq : (↑(U z v) : v.adicCompletion K) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent z v :=
        RestrictedProduct.unitsEquiv_apply v z
      rw [heq]
      change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
        (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder z v) = 1
      rw [hv]
      simp
    have hfactor : ∀ (a b : (Chapter09FiniteAdele K)ˣ)
        (v : HeightOneSpectrum (𝓞 K)),
        chapter09FiniteNormUnit v (U (a * b) v) =
          chapter09FiniteNormUnit v (U a v) * chapter09FiniteNormUnit v (U b v) := by
      intro a b v
      apply Units.ext
      change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
          (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
            (↑(U (a * b) v) : v.adicCompletion K)) =
        (Ideal.absNorm v.asIdeal : ℝ≥0) ^
            (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
              (↑(U a v) : v.adicCompletion K)) *
          (Ideal.absNorm v.asIdeal : ℝ≥0) ^
            (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
              (↑(U b v) : v.adicCompletion K))
      have horder : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          (↑(U (a * b) v) : v.adicCompletion K) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
            (↑(U a v) : v.adicCompletion K) +
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
              (↑(U b v) : v.adicCompletion K) := by
        have hab : (↑(U (a * b) v) : v.adicCompletion K) =
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
              (a * b) v := RestrictedProduct.unitsEquiv_apply v (a * b)
        have ha : (↑(U a v) : v.adicCompletion K) =
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent a v :=
          RestrictedProduct.unitsEquiv_apply v a
        have hb : (↑(U b v) : v.adicCompletion K) =
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent b v :=
          RestrictedProduct.unitsEquiv_apply v b
        rw [hab, ha, hb]
        change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder (a * b) v =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder a v +
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder b v
        exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_order_mul a b v
      rw [horder, neg_add,
        zpow_add₀ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)]
    have hfinite : ∀ (a b : (Chapter09FiniteAdele K)ˣ),
        chapter09FiniteIdeleModule (a * b) =
          chapter09FiniteIdeleModule a * chapter09FiniteIdeleModule b := by
      intro a b
      unfold chapter09FiniteIdeleModule
      change (∏ᶠ v : HeightOneSpectrum (𝓞 K), chapter09FiniteNormUnit v (U (a * b) v)) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), chapter09FiniteNormUnit v (U a v)) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 K), chapter09FiniteNormUnit v (U b v)
      rw [← finprod_mul_distrib (hsupport a) (hsupport b)]
      apply finprod_congr
      intro v
      exact hfactor a b v
    have hinfinite : ∀ (a b : (Chapter09InfiniteAdele K)ˣ),
        chapter09InfiniteIdeleModule (a * b) =
          chapter09InfiniteIdeleModule a * chapter09InfiniteIdeleModule b := by
      intro a b
      unfold chapter09InfiniteIdeleModule
      have hpi : MulEquiv.piUnits (a * b) = MulEquiv.piUnits a * MulEquiv.piUnits b :=
        (MulEquiv.piUnits).map_mul a b
      rw [hpi, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      simp only [Pi.mul_apply]
      have hnorm : chapter09NormUnit ((MulEquiv.piUnits a) v *
          (MulEquiv.piUnits b) v) =
          chapter09NormUnit ((MulEquiv.piUnits a) v) *
            chapter09NormUnit ((MulEquiv.piUnits b) v) :=
        (chapter09NormUnitHom).map_mul _ _
      rw [hnorm, mul_pow]
    change chapter09IdeleModule (x * y) =
      chapter09IdeleModule x * chapter09IdeleModule y
    change chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K
      (x * y)).1) * chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K
      (x * y)).2) = (chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K
      x).1) * chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K x).2)) *
        (chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K y).1) *
          chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K y).2))
    rw [(chapter09IdeleProductEquiv K).map_mul]
    change chapter09InfiniteIdeleModule ((chapter09IdeleProductEquiv K x).1 *
        (chapter09IdeleProductEquiv K y).1) *
      chapter09FiniteIdeleModule ((chapter09IdeleProductEquiv K x).2 *
        (chapter09IdeleProductEquiv K y).2) = _
    rw [hinfinite, hfinite]
    ac_rfl

@[simp]
theorem chapter09IdeleModuleHom_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleModuleHom K x = chapter09IdeleModule x :=
  rfl

/-- The idele module viewed as an `ℝ≥0`-valued homomorphism. -/
def chapter09IdeleModuleNNRealHom
    (K : Type*) [Field K] [NumberField K] :
    Chapter09Idele K →* ℝ≥0 :=
  (Units.coeHom ℝ≥0).comp (chapter09IdeleModuleHom K)

@[simp]
theorem chapter09IdeleModuleNNRealHom_apply
    {K : Type*} [Field K] [NumberField K] (x : Chapter09Idele K) :
    chapter09IdeleModuleNNRealHom K x =
      (chapter09IdeleModuleHom K x : ℝ≥0) :=
  rfl

/- The action used by `distribHaarChar` is the canonical multiplication action
of adele units on the additive adele ring. -/
theorem chapter09IdeleModuleNNRealHom_eq_distribHaarChar
    (K : Type*) [Field K] [NumberField K] :
    chapter09IdeleModuleNNRealHom K =
      MeasureTheory.distribHaarChar
        (G := Chapter09Idele K) (A := Chapter09Adele K) := by
  sorry

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
  map_one' := by
    change (chapter09IdeleProductEquiv K (1 : Chapter09Idele K)).2 = 1
    rw [(chapter09IdeleProductEquiv K).map_one]
    rfl
  map_mul' x y := by
    change (chapter09IdeleProductEquiv K (x * y)).2 =
      (chapter09IdeleProductEquiv K x).2 * (chapter09IdeleProductEquiv K y).2
    rw [(chapter09IdeleProductEquiv K).map_mul]
    rfl

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
    intro a
    have hfinite : chapter09FinitePrincipalIdele K a =
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
      apply Units.ext
      rfl
    change ClassGroup.mk K
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
        (chapter09FinitePrincipalIdele K a)) = 1
    rw [hfinite,
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal]
    apply (ClassGroup.mk_eq_one_iff).2
    refine ⟨(a : K), ?_⟩
    simp [coe_toPrincipalIdeal]
  kernel_eq_principal_mul_units := by
    classical
    ext x
    constructor
    · intro hx
      change ClassGroup.mk K
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K x) = 1 at hx
      have hclass' := congrArg (ClassGroup.equiv K) hx
      rw [ClassGroup.equiv_mk, map_one] at hclass'
      let I : LastLib.Book04AdelesAndIdeles.Chapter08.Chapter08IdealGroup K :=
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K x
      have hI : QuotientGroup.mk'
          (toPrincipalIdeal (𝓞 K) K).range I = 1 := by
        simpa [I] using hclass'
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hI
      obtain ⟨a, ha⟩ := hI
      have hpa : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
          (chapter09FinitePrincipalIdele K a) = toPrincipalIdeal (𝓞 K) K a := by
        have hfinite : chapter09FinitePrincipalIdele K a =
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
          apply Units.ext
          rfl
        rw [hfinite]
        exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal a
      let y : (Chapter09FiniteAdele K)ˣ :=
        x * (chapter09FinitePrincipalIdele K a)⁻¹
      have hyideal :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K y = 1 := by
        simp [y]
        rw [hpa, ha]
        change I * I⁻¹ = 1
        simp
      have hy : y ∈ chapter09FiniteUnitIdeles K := by
        change y ∈
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits
        rw [← LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
        exact (MonoidHom.mem_ker).2 hyideal
      apply Subgroup.mem_sup.mpr
      refine ⟨chapter09FinitePrincipalIdele K a, ⟨a, rfl⟩, y, hy, ?_⟩
      simp [y, mul_left_comm]
    · intro hx
      change ClassGroup.mk K
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K x) = 1
      rcases Subgroup.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
      rcases hy with ⟨a, rfl⟩
      have hfinite : chapter09FinitePrincipalIdele K a =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a := by
        apply Units.ext
        rfl
      have hpa : LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
          (chapter09FinitePrincipalIdele K a) = toPrincipalIdeal (𝓞 K) K a := by
        rw [hfinite]
        exact LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal a
      have hz' :
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K z = 1 := by
        change z ∈
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits at hz
        apply (MonoidHom.mem_ker).1
        rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
        exact hz
      rw [map_mul, hpa, hz', mul_one]
      apply (ClassGroup.mk_eq_one_iff).2
      refine ⟨(a : K), ?_⟩
      simp [coe_toPrincipalIdeal]
  surjective := by
    intro c
    refine ClassGroup.induction (R := 𝓞 K) K (fun I => ?_) c
    obtain ⟨x, hx⟩ :=
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_surjective K I
    exact ⟨x, congrArg (ClassGroup.mk K) hx⟩

theorem chapter09FiniteUnitIdeles_mem_iff
    {K : Type*} [Field K] [NumberField K]
    {x : (Chapter09FiniteAdele K)ˣ} :
    x ∈ chapter09FiniteUnitIdeles K ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        chapter09FiniteNormUnit v
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) = 1 := by
  constructor
  · intro hx v
    have hv : (Valued.v (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent x v) :
        WithZero (Multiplicative ℤ)) = 1 := by
      exact (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
        x).1 hx v
    have horder :=
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
        v (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent x v)
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_component_ne_zero x v)).2 hv
    apply Units.ext
    change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v)) = 1
    have hcomp :
        (↑((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) :
          v.adicCompletion K) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent x v :=
      RestrictedProduct.unitsEquiv_apply v x
    rw [hcomp, horder]
    simp
  · intro hx
    apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
      x).2
    intro v
    have hv := congrArg Units.val (hx v)
    change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        ((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v)) = 1 at hv
    have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
      ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)
    have horder :
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
          ((RestrictedProduct.unitsEquiv
            (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) = 0 := by
      rw [zpow_eq_one_iff_right₀ (by positivity) hq] at hv
      exact neg_eq_zero.mp hv
    have hcomp :
        (↑((RestrictedProduct.unitsEquiv
          (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) x) v) :
          v.adicCompletion K) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent x v :=
      RestrictedProduct.unitsEquiv_apply v x
    rw [← hcomp]
    exact (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_local_order_eq_zero_iff_valued_eq_one
      v _ (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_component_ne_zero x v)).1
      horder

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
  have hdecomp : chapter09IdeleProductEquiv K (chapter09PrincipalIdele K a) =
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a,
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) := by
    apply Prod.ext <;> rfl
  rw [chapter09IdeleModule_eq_infinite_mul_finite, hdecomp]
  apply Units.ext
  change (chapter09InfiniteIdeleModule
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a) :
        ℝ≥0) *
      (chapter09FiniteIdeleModule
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) :
        ℝ≥0) = 1
  have hinf :
      (chapter09InfiniteIdeleModule
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a) :
        ℝ≥0) = ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊ := by
    let x : (Chapter09InfiniteAdele K)ˣ :=
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele a
    change (Units.coeHom ℝ≥0)
        (∏ v : InfinitePlace K,
          chapter09NormUnit
            (MulEquiv.piUnits x v) ^
            v.mult) = ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊
    rw [map_prod]
    simp [chapter09NormUnit]
    have hfactor : ∀ v : InfinitePlace K,
        ‖((MulEquiv.piUnits x v).val : v.Completion)‖₊ ^ v.mult =
          ‖v (a : K)‖₊ ^ v.mult := by
      intro v
      simp [x, MulEquiv.piUnits,
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08InfinitePrincipalIdele]
      apply NNReal.eq
      simp only [coe_nnnorm]
      rw [NumberField.InfinitePlace.Completion.norm_coe]
      change v (a : K) = ‖v (a : K)‖
      rw [Real.norm_eq_abs, abs_of_pos (InfinitePlace.pos_iff.mpr a.ne_zero)]
    have hinfprod :
        (∏ v : InfinitePlace K,
          ‖((MulEquiv.piUnits x v).val : v.Completion)‖₊ ^ v.mult) =
          ∏ v : InfinitePlace K, ‖v (a : K)‖₊ ^ v.mult := by
      apply Finset.prod_congr rfl
      intro v hv
      exact hfactor v
    rw [hinfprod]
    have hprod :
        (∏ v : InfinitePlace K, ‖v (a : K)‖₊ ^ v.mult) =
          ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊ := by
      apply NNReal.eq
      simpa only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm,
        Real.norm_eq_abs, abs_of_pos (InfinitePlace.pos_iff.mpr a.ne_zero), Rat.cast_abs] using
        (NumberField.InfinitePlace.prod_eq_abs_norm (a : K))
    exact hprod
  have hnorm :
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleNorm
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) =
        (|Algebra.norm ℚ (a : K)| : ℚ)⁻¹ := by
    rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_norm_product_formula,
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal]
    simp [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08IdealNorm, coe_toPrincipalIdeal]
  have hsupportRat : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (Ideal.absNorm v.asIdeal : ℚ) ^
          (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v)) := by
    rw [Function.HasFiniteMulSupport]
    apply Filter.eventually_cofinite.mp
    filter_upwards [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_order_eventually_eq_zero
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a)] with v hv
    simp [hv]
  have hnormReal :
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleNorm
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) : ℝ) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((Ideal.absNorm v.asIdeal : ℚ) ^
            (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) : ℝ) := by
    unfold LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleNorm
    change (Rat.castHom ℝ).toMonoidHom
        (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (Ideal.absNorm v.asIdeal : ℚ) ^
            (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v)) = _
    rw [(Rat.castHom ℝ).toMonoidHom.map_finprod hsupportRat]
    apply finprod_congr
    intro v
    simp
  let U := RestrictedProduct.unitsEquiv
    (𝓕 := Filter.cofinite)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
  have hsupport : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        chapter09FiniteNormUnit v
          (U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v)) := by
    rw [Function.HasFiniteMulSupport]
    apply Filter.eventually_cofinite.mp
    filter_upwards [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_order_eventually_eq_zero
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a)] with v hv
    apply Units.ext
    change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
        (↑(U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) :
          v.adicCompletion K)) = 1
    have heq : (↑(U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) :
        v.adicCompletion K) =
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v :=
      RestrictedProduct.unitsEquiv_apply v _
    rw [heq]
    change (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
        (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) = 1
    rw [hv]
    simp
  have hfin :
      (chapter09FiniteIdeleModule
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) : ℝ≥0) =
        ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊⁻¹ := by
    apply NNReal.eq
    change ((Units.coeHom ℝ≥0)
        (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          chapter09FiniteNormUnit v
            (U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v)) :
          ℝ) = ‖(Algebra.norm ℚ (a : K) : ℝ)‖₊⁻¹
    rw [(Units.coeHom ℝ≥0).map_finprod hsupport]
    have hsupportNN : Function.HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          (Units.coeHom ℝ≥0)
            (chapter09FiniteNormUnit v
              (U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v))) := by
      rw [Function.HasFiniteMulSupport]
      refine hsupport.subset ?_
      intro v hv
      by_contra hv0
      apply hv
      have hunit : chapter09FiniteNormUnit v
            (U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) = 1 :=
        not_ne_iff.mp hv0
      simp [hunit]
    change (NNReal.toRealHom.toMonoidHom)
        (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (Units.coeHom ℝ≥0)
            (chapter09FiniteNormUnit v
          (U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v))) = _
    rw [NNReal.toRealHom.toMonoidHom.map_finprod hsupportNN]
    simp [NNReal.toRealHom, chapter09FiniteNormUnit]
    have hcomp : ∀ v : HeightOneSpectrum (𝓞 K),
        (↑(U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) :
          v.adicCompletion K) =
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleComponent
            (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v := by
      intro v
      exact RestrictedProduct.unitsEquiv_apply v _
    have hfactor : ∀ v : HeightOneSpectrum (𝓞 K),
        ((Ideal.absNorm v.asIdeal : ℝ) ^
          LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
            (↑(U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) :
              v.adicCompletion K))⁻¹ =
          (Ideal.absNorm v.asIdeal : ℝ) ^
            (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
              (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) := by
      intro v
      rw [hcomp v, zpow_neg]
      rfl
    calc
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((Ideal.absNorm v.asIdeal : ℝ) ^
            LastLib.Book04AdelesAndIdeles.Chapter08.chapter08LocalOrder v
              (↑(U (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) :
                v.adicCompletion K))⁻¹) =
          ∏ᶠ v : HeightOneSpectrum (𝓞 K),
            (Ideal.absNorm v.asIdeal : ℝ) ^
              (-LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleOrder
                (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) v) := by
        apply finprod_congr
        intro v
        exact hfactor v
      _ = (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleNorm
          (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele a) : ℝ) :=
        hnormReal.symm
      _ = ‖(Algebra.norm ℚ (a : K) : ℝ)‖⁻¹ := by
        rw [hnorm]
        simp only [Rat.cast_inv, Rat.cast_abs]
        rw [Real.norm_eq_abs]
  rw [hinf, hfin]
  have hnorm0 : (Algebra.norm ℚ (a : K) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr a.ne_zero)
  exact mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hnorm0)

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
    change chapter09IdeleModule (chapter09PrincipalIdele K a) = 1
    exact chapter09PrincipalIdele_module_eq_one a⟩
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
      rcases hx with ⟨a, rfl⟩
      change chapter09IdeleModule (chapter09PrincipalIdele K a) = 1
      exact chapter09PrincipalIdele_module_eq_one a)

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
  let φ : chapter09NormOneIdeles K →* chapter09ClassNormOne K := {
    toFun x := ⟨QuotientGroup.mk x, by
      change chapter09IdeleClassModule K (QuotientGroup.mk x) = 1
      rw [chapter09IdeleClassModule_apply]
      exact (chapter09NormOneIdeles_mem_iff).1 x.property⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      ext
      simp
  }
  have hsurj : Function.Surjective φ := by
    intro z
    rcases QuotientGroup.mk_surjective z.1 with ⟨g, hg⟩
    have hmodule : chapter09IdeleClassModule K (QuotientGroup.mk g) = 1 := by
      rw [hg]
      exact z.property
    have hnorm : g ∈ chapter09NormOneIdeles K := by
      change chapter09IdeleModuleHom K g = 1
      rw [chapter09IdeleModuleHom_apply]
      exact hmodule
    refine ⟨⟨g, hnorm⟩, ?_⟩
    apply Subtype.ext
    exact hg
  have hker : (chapter09NormOnePrincipalIdele K).range = φ.ker := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      change φ (chapter09NormOnePrincipalIdele K a) = 1
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff _).2
      exact ⟨a, rfl⟩
    · intro hx
      have hx' : φ x = 1 := hx
      have hclass : (x.1 : Chapter09IdeleClassGroup K) = 1 := by
        exact congrArg Subtype.val hx'
      have hp : x.1 ∈ chapter09PrincipalIdeleSubgroup K :=
        (QuotientGroup.eq_one_iff _).1 hclass
      rcases hp with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha
  exact QuotientGroup.liftEquiv (chapter09NormOnePrincipalIdele K).range hsurj hker

/-! The compactness arguments use the quotient topology on both sides, so the
algebraic identification above also needs its topological form. -/
noncomputable def chapter09NormOneClassGroup_continuousEquiv_classNormOne
    {K : Type*} [Field K] [NumberField K] :
    Chapter09NormOneClassGroup K ≃ₜ* chapter09ClassNormOne K := by
  classical
  let N := chapter09NormOneIdeles K
  let P := (chapter09NormOnePrincipalIdele K).range
  let P₀ := chapter09PrincipalIdeleSubgroup K
  let e := chapter09NormOneClassGroup_equiv_classNormOne (K := K)
  let g : Chapter09NormOneClassGroup K →* Chapter09IdeleClassGroup K :=
    (chapter09ClassNormOne K).subtype.comp e.toMonoidHom
  have hcomm :
      g.comp (QuotientGroup.mk' P) =
        (QuotientGroup.mk' P₀).comp N.subtype := by
    ext x
    rfl
  have hsat :
      (QuotientGroup.mk' P₀ : Chapter09Idele K → Chapter09IdeleClassGroup K) ⁻¹'
          (QuotientGroup.mk' P₀ '' Set.range N.subtype) ⊆ Set.range N.subtype := by
    intro x hx
    rcases hx with ⟨y, ⟨z, rfl⟩, hxy⟩
    have hp : x / (z : Chapter09Idele K) ∈ P₀ :=
      (QuotientGroup.eq_iff_div_mem).1 hxy.symm
    rcases hp with ⟨a, ha⟩
    have hfactor : x = chapter09PrincipalIdele K a * (z : Chapter09Idele K) := by
      have h := congrArg (fun w : Chapter09Idele K => w * (z : Chapter09Idele K)) ha
      simpa [div_eq_mul_inv, mul_assoc] using h.symm
    have hxnorm : x ∈ N := by
      change chapter09IdeleModuleHom K x = 1
      have hz : chapter09IdeleModule (z : Chapter09Idele K) = 1 := by
        change chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1
        exact z.property
      have hpa : chapter09IdeleModuleHom K (chapter09PrincipalIdele K a) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using
          chapter09PrincipalIdele_module_eq_one a
      have hz' : chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using hz
      rw [hfactor, (chapter09IdeleModuleHom K).map_mul, hpa, hz']
      simp
    exact ⟨⟨x, hxnorm⟩, rfl⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply e.injective
    exact Subtype.ext hxy
  have hcomm_fun :
      (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K) ∘
          (QuotientGroup.mk : N →
            Chapter09NormOneClassGroup K) =
          (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K) ∘
          N.subtype := by
    ext x
    exact congrArg (fun h : N →* Chapter09IdeleClassGroup K => h x) hcomm
  have hgemb : IsEmbedding g :=
    isEmbedding_of_isOpenQuotientMap_of_isInducing
      (f := (N.subtype : N → Chapter09Idele K))
      (g := (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K))
      (p := (QuotientGroup.mk : N → Chapter09NormOneClassGroup K))
      (q := (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K))
      hcomm_fun IsInducing.subtypeVal (QuotientGroup.isQuotientMap_mk P)
      (QuotientGroup.isOpenQuotientMap_mk (N := P₀)) hg_inj hsat
  have hemb : IsEmbedding (e : Chapter09NormOneClassGroup K →
      chapter09ClassNormOne K) := by
    exact (Topology.IsEmbedding.of_comp_iff (f := e)
      (g := (chapter09ClassNormOne K).subtype) IsEmbedding.subtypeVal).mp hgemb
  exact ContinuousMulEquiv.mk e hemb.continuous
    (hemb.toHomeomorphOfSurjective e.surjective).symm.continuous

theorem chapter09NormOneClassGroup_equiv_classNormOne_continuous
    {K : Type*} [Field K] [NumberField K] :
    Continuous (chapter09NormOneClassGroup_equiv_classNormOne (K := K) :
      Chapter09NormOneClassGroup K → chapter09ClassNormOne K) := by
  classical
  let N := chapter09NormOneIdeles K
  let P := (chapter09NormOnePrincipalIdele K).range
  let P₀ := chapter09PrincipalIdeleSubgroup K
  let e := chapter09NormOneClassGroup_equiv_classNormOne (K := K)
  let g : Chapter09NormOneClassGroup K →* Chapter09IdeleClassGroup K :=
    (chapter09ClassNormOne K).subtype.comp e.toMonoidHom
  have hcomm :
      g.comp (QuotientGroup.mk' P) =
        (QuotientGroup.mk' P₀).comp N.subtype := by
    ext x
    rfl
  have hsat :
      (QuotientGroup.mk' P₀ : Chapter09Idele K → Chapter09IdeleClassGroup K) ⁻¹'
          (QuotientGroup.mk' P₀ '' Set.range N.subtype) ⊆ Set.range N.subtype := by
    intro x hx
    rcases hx with ⟨y, ⟨z, rfl⟩, hxy⟩
    have hp : x / (z : Chapter09Idele K) ∈ P₀ :=
      (QuotientGroup.eq_iff_div_mem).1 hxy.symm
    rcases hp with ⟨a, ha⟩
    have hfactor : x = chapter09PrincipalIdele K a * (z : Chapter09Idele K) := by
      have h := congrArg (fun w : Chapter09Idele K => w * (z : Chapter09Idele K)) ha
      simpa [div_eq_mul_inv, mul_assoc] using h.symm
    have hxnorm : x ∈ N := by
      change chapter09IdeleModuleHom K x = 1
      have hz : chapter09IdeleModule (z : Chapter09Idele K) = 1 := by
        change chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1
        exact z.property
      have hpa : chapter09IdeleModuleHom K (chapter09PrincipalIdele K a) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using
          chapter09PrincipalIdele_module_eq_one a
      have hz' : chapter09IdeleModuleHom K (z : Chapter09Idele K) = 1 := by
        simpa only [chapter09IdeleModuleHom_apply] using hz
      rw [hfactor, (chapter09IdeleModuleHom K).map_mul, hpa, hz']
      simp
    exact ⟨⟨x, hxnorm⟩, rfl⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    apply e.injective
    exact Subtype.ext hxy
  have hcomm_fun :
      (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K) ∘
          (QuotientGroup.mk : N →
            Chapter09NormOneClassGroup K) =
          (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K) ∘
          N.subtype := by
    ext x
    exact congrArg (fun h : N →* Chapter09IdeleClassGroup K => h x) hcomm
  have hgemb : IsEmbedding g :=
    isEmbedding_of_isOpenQuotientMap_of_isInducing
      (f := (N.subtype : N → Chapter09Idele K))
      (g := (g : Chapter09NormOneClassGroup K → Chapter09IdeleClassGroup K))
      (p := (QuotientGroup.mk : N → Chapter09NormOneClassGroup K))
      (q := (QuotientGroup.mk : Chapter09Idele K → Chapter09IdeleClassGroup K))
      hcomm_fun IsInducing.subtypeVal (QuotientGroup.isQuotientMap_mk P)
      (QuotientGroup.isOpenQuotientMap_mk (N := P₀)) hg_inj hsat
  have hemb : IsEmbedding (e : Chapter09NormOneClassGroup K →
      chapter09ClassNormOne K) := by
    exact (Topology.IsEmbedding.of_comp_iff (f := e)
      (g := (chapter09ClassNormOne K).subtype) IsEmbedding.subtypeVal).mp hgemb
  exact hemb.continuous

/-! ### Finite unit ideles and the archimedean norm-one subgroup -/

def chapter09FiniteUnitIdeleEmbedding
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09FiniteAdele K)ˣ →* Chapter09Idele K where
  toFun u :=
    (chapter09IdeleProductEquiv K).symm (1, u)
  map_one' := by
    change (chapter09IdeleProductEquiv K).symm (1, 1) = 1
    simp
  map_mul' x y := by
    change (chapter09IdeleProductEquiv K).symm (1, x * y) =
      (chapter09IdeleProductEquiv K).symm (1, x) *
        (chapter09IdeleProductEquiv K).symm (1, y)
    rw [← (chapter09IdeleProductEquiv K).symm.map_mul]
    simp

def chapter09FiniteUnitIdeleSubgroup
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  Subgroup.map (chapter09FiniteUnitIdeleEmbedding K)
    (chapter09FiniteUnitIdeles K)

theorem chapter09FiniteUnitIdele_module_eq_one
    {K : Type*} [Field K] [NumberField K]
    (u : chapter09FiniteUnitIdeles K) :
    chapter09IdeleModule (chapter09FiniteUnitIdeleEmbedding K u) = 1 := by
  have hdecomp : chapter09IdeleProductEquiv K
      (chapter09FiniteUnitIdeleEmbedding K u) = (1, (u : (Chapter09FiniteAdele K)ˣ)) := by
    simp [chapter09FiniteUnitIdeleEmbedding]
  have hinf : chapter09InfiniteIdeleModule
      (1 : (Chapter09InfiniteAdele K)ˣ) = 1 := by
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    simp [chapter09NormUnit]
  have hfin : chapter09FiniteIdeleModule (u : (Chapter09FiniteAdele K)ˣ) = 1 := by
    unfold chapter09FiniteIdeleModule
    apply finprod_eq_one_of_forall_eq_one
    intro v
    exact (chapter09FiniteUnitIdeles_mem_iff.mp u.property v)
  rw [chapter09IdeleModule_eq_infinite_mul_finite, hdecomp, hinf, hfin]
  simp

def chapter09PrincipalTimesFiniteUnits
    (K : Type*) [Field K] [NumberField K] : Subgroup (Chapter09Idele K) :=
  chapter09PrincipalIdeleSubgroup K ⊔ chapter09FiniteUnitIdeleSubgroup K

def chapter09InfiniteIdeleModuleHom
    (K : Type*) [Field K] [NumberField K] :
    (Chapter09InfiniteAdele K)ˣ →* Chapter09PositiveReal where
  toFun := chapter09InfiniteIdeleModule
  map_one' := by
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits (1 : (Chapter09InfiniteAdele K)ˣ) = 1 :=
      (MulEquiv.piUnits).map_one
    rw [hpi]
    simp [chapter09NormUnit]
  map_mul' x y := by
    classical
    unfold chapter09InfiniteIdeleModule
    have hpi : MulEquiv.piUnits (x * y) = MulEquiv.piUnits x * MulEquiv.piUnits y :=
      (MulEquiv.piUnits).map_mul x y
    rw [hpi, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [Pi.mul_apply]
    have hnorm : chapter09NormUnit ((MulEquiv.piUnits x) v *
        (MulEquiv.piUnits y) v) =
        chapter09NormUnit ((MulEquiv.piUnits x) v) *
          chapter09NormUnit ((MulEquiv.piUnits y) v) :=
      (chapter09NormUnitHom).map_mul _ _
    rw [hnorm, mul_pow]

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
    change chapter09InfiniteIdeleModule (chapter09InfiniteUnitEmbedding K u) = 1
    apply Units.ext
    unfold chapter09InfiniteIdeleModule
    change (Units.coeHom ℝ≥0)
        (∏ v : InfinitePlace K,
          chapter09NormUnit (MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u) v) ^ v.mult) = 1
    rw [map_prod]
    simp [chapter09NormUnit]
    apply NNReal.eq
    simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm, NNReal.coe_one]
    have hfactor : ∀ v : InfinitePlace K,
        ‖(↑(MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u) v) : v.Completion)‖ =
          v (u : K) := by
      intro v
      change ‖((u : K) : v.Completion)‖ = v (u : K)
      rw [← (WithAbs.equiv v.1).apply_symm_apply (u : K),
        NumberField.InfinitePlace.Completion.norm_coe]
      rfl
    have hinfprod :
        (∏ v : InfinitePlace K,
          ‖(↑(MulEquiv.piUnits (chapter09InfiniteUnitEmbedding K u) v) : v.Completion)‖ ^ v.mult) =
          ∏ v : InfinitePlace K, (v (u : K)) ^ v.mult := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [hfactor v]
    rw [hinfprod]
    simpa only [NumberField.Units.norm, Rat.cast_one] using
      (NumberField.InfinitePlace.prod_eq_abs_norm (u : K))⟩
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
    change chapter09FiniteUnitEmbedding K u ∈
      LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIntegralUnits
    rw [← LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_kernel]
    apply (MonoidHom.mem_ker).2
    change LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleIdealMap K
      (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FinitePrincipalIdele
        (Units.map (algebraMap (𝓞 K) K) u)) = 1
    rw [LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_idele_ideal_principal]
    apply Units.ext
    apply FractionalIdeal.coeToSubmodule_injective
    have hspan : Submodule.span (𝓞 K)
        {((algebraMap (𝓞 K) K) (u : 𝓞 K))} = 1 :=
      (Submodule.span_singleton_eq_one_iff).2 ⟨u, rfl⟩
    simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hspan⟩
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
      change chapter09IdeleModule
        ((chapter09IdeleProductEquiv K).symm (x.1.1, x.2.1)) = 1
      rw [chapter09IdeleModule_eq_infinite_mul_finite]
      change chapter09InfiniteIdeleModule x.1.1 *
        chapter09FiniteIdeleModule x.2.1 = 1
      have hinf : chapter09InfiniteIdeleModule x.1.1 = 1 := by
        change chapter09InfiniteIdeleModuleHom K x.1.1 = 1
        exact x.1.2
      have hfin : chapter09FiniteIdeleModule x.2.1 = 1 := by
        unfold chapter09FiniteIdeleModule
        apply finprod_eq_one_of_forall_eq_one
        intro v
        exact (chapter09FiniteUnitIdeles_mem_iff).1 x.2.2 v
      rw [hinf, hfin, one_mul]⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rfl

def chapter09ArchFiniteToNormOneClassGroup
    (K : Type*) [Field K] [NumberField K] :
    Chapter09ArchFiniteUnitKernel K →* Chapter09NormOneClassGroup K :=
  QuotientGroup.lift (chapter09GlobalUnitDiagonal K).range
    ((QuotientGroup.mk' (chapter09NormOnePrincipalIdele K).range).comp
      (chapter09ArchFiniteToNormOneIdele K)) (by
      intro x hx
      rcases hx with ⟨u, rfl⟩
      apply (QuotientGroup.eq_one_iff _).2
      refine ⟨Units.map (algebraMap (𝓞 K) K) u, ?_⟩
      apply Subtype.ext
      rfl)

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
