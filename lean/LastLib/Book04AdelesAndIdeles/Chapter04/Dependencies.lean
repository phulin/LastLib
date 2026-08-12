import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Profinite
import LastLib.Book04AdelesAndIdeles.Chapter01.Section04Approximation
import LastLib.Book04AdelesAndIdeles.Chapter01.Section05IdealLatticesAndDiscriminants
import LastLib.Book04AdelesAndIdeles.Chapter02.Section06LocalDegreesOverARationalPlace
import LastLib.Book04AdelesAndIdeles.Chapter03.Section07DependenceOnDistinguishedSubgroups

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter Function
open NumberField IsDedekindDomain
open scoped BigOperators Pointwise TensorProduct Topology RestrictedProduct

universe uK uV uW uι

/-!
Shared canonical interfaces for Chapter 4.

The adele carriers below are the pinned Mathlib carriers.  The additional
definitions retain the local coordinates and integral models explicitly so
that the source-order section files can state the restricted-product maps,
quotients, and linear-algebra comparisons without replacing canonical objects
by parallel ad hoc types.
-/

abbrev Chapter04RingOfIntegers (K : Type uK) [Field K] [NumberField K] :=
  𝓞 K

abbrev Chapter04FinitePlace (K : Type uK) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

abbrev Chapter04InfinitePlace (K : Type uK) [Field K] [NumberField K] :=
  NumberField.InfinitePlace K

abbrev Chapter04Place (K : Type uK) [Field K] [NumberField K] :=
  Chapter04FinitePlace K ⊕ Chapter04InfinitePlace K

abbrev Chapter04FiniteLocalField
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) : Type _ :=
  v.adicCompletion K

abbrev Chapter04FiniteLocalIntegerRing
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) : Type _ :=
  v.adicCompletionIntegers K

def chapter04FiniteLocalIntegerSet
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) : Set (Chapter04FiniteLocalField K v) :=
  (v.adicCompletionIntegers K : Set (v.adicCompletion K))

abbrev Chapter04FiniteAdeleRing (K : Type uK) [Field K] [NumberField K] :=
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

abbrev Chapter04InfiniteAdeleRing (K : Type uK) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K

abbrev Chapter04AdeleRing (K : Type uK) [Field K] [NumberField K] :=
  NumberField.AdeleRing (𝓞 K) K

/- The full adele ring of an extension is canonically a base-field algebra
   by restricting its native algebra structure along the field extension. -/
instance chapter04AdeleRingAlgebraOver
    (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] :
    Algebra K (Chapter04AdeleRing L) :=
  Algebra.compHom (Chapter04AdeleRing L) (algebraMap K L)

abbrev Chapter04FiniteAdeleCoordinate
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) :=
  Chapter04FiniteLocalField K v

def chapter04FiniteAdeleExceptionalSet
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) : Set (Chapter04FinitePlace K) :=
  {v | x v ∉ chapter04FiniteLocalIntegerSet K v}

theorem chapter04_finiteAdele_mem_iff_eventually_integral
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    ∀ᶠ v : Chapter04FinitePlace K in Filter.cofinite,
      x v ∈ chapter04FiniteLocalIntegerSet K v :=
  by
    sorry

theorem chapter04_finiteAdele_exceptionalSet_finite
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    (chapter04FiniteAdeleExceptionalSet K x).Finite := by
  sorry

theorem chapter04_finiteAdele_add_apply
    (K : Type uK) [Field K] [NumberField K]
    (x y : Chapter04FiniteAdeleRing K) (v : Chapter04FinitePlace K) :
    (x + y) v = x v + y v := by
  rfl

theorem chapter04_finiteAdele_mul_apply
    (K : Type uK) [Field K] [NumberField K]
    (x y : Chapter04FiniteAdeleRing K) (v : Chapter04FinitePlace K) :
    (x * y) v = x v * y v := by
  rfl

theorem chapter04_finiteAdele_zero_apply
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) :
    (0 : Chapter04FiniteAdeleRing K) v = 0 := by
  rfl

theorem chapter04_finiteAdele_one_apply
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) :
    (1 : Chapter04FiniteAdeleRing K) v = 1 := by
  rfl

@[ext]
theorem chapter04_finiteAdele_ext
    (K : Type uK) [Field K] [NumberField K]
    {x y : Chapter04FiniteAdeleRing K}
    (h : ∀ v : Chapter04FinitePlace K, x v = y v) :
    x = y :=
  IsDedekindDomain.FiniteAdeleRing.ext K h

abbrev Chapter04FiniteIntegralAdele (K : Type uK) [Field K] [NumberField K] :=
  ∀ v : Chapter04FinitePlace K, Chapter04FiniteLocalIntegerRing K v

def chapter04FiniteIntegralAdeleEmbedding
    (K : Type uK) [Field K] [NumberField K] :
    Chapter04FiniteIntegralAdele K →+* Chapter04FiniteAdeleRing K where
  toFun x :=
    ⟨(fun v : Chapter04FinitePlace K => x v),
      Filter.Eventually.of_forall (fun v => (x v).property)⟩
  map_one' := by
    ext v
    rfl
  map_mul' x y := by
    ext v
    rfl
  map_zero' := by
    ext v
    rfl
  map_add' x y := by
    ext v
    rfl

abbrev Chapter04FiniteIntegralAdeleSubring
    (K : Type uK) [Field K] [NumberField K] :
    Subring (Chapter04FiniteAdeleRing K) :=
  (chapter04FiniteIntegralAdeleEmbedding K).range

abbrev Chapter04HatRingOfIntegers
    (K : Type uK) [Field K] [NumberField K] :
    Subring (Chapter04FiniteAdeleRing K) :=
  Chapter04FiniteIntegralAdeleSubring K

abbrev Chapter04FiniteIntegralAdeleAddSubgroup
    (K : Type uK) [Field K] [NumberField K] :
    AddSubgroup (Chapter04FiniteAdeleRing K) :=
  (Chapter04FiniteIntegralAdeleSubring K).toAddSubgroup

theorem chapter04_finiteIntegralAdele_mem_iff_all_coordinates_integral
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    x ∈ Chapter04FiniteIntegralAdeleSubring K ↔
      ∀ v : Chapter04FinitePlace K,
        x v ∈ chapter04FiniteLocalIntegerSet K v := by
  sorry

theorem chapter04_finiteIntegralAdele_is_compact_open
    (K : Type uK) [Field K] [NumberField K] :
    IsCompact (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) ∧
      IsOpen (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

theorem chapter04_finiteIntegralAdele_is_profinite_topological_ring
    (K : Type uK) [Field K] [NumberField K] :
    CompactSpace (Chapter04FiniteIntegralAdele K) ∧
      T2Space (Chapter04FiniteIntegralAdele K) ∧
      TotallyDisconnectedSpace (Chapter04FiniteIntegralAdele K) := by
  sorry

theorem chapter04_finiteAdeleRing_is_locally_compact_topological_ring
    (K : Type uK) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter04FiniteAdeleRing K) ∧
      IsTopologicalRing (Chapter04FiniteAdeleRing K) := by
  sorry

def chapter04LocalField
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04Place K) : Type _ :=
  match v with
  | Sum.inl w => Chapter04FiniteLocalField K w
  | Sum.inr w => w.Completion

instance chapter04LocalFieldTopologicalSpace
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04Place K) : TopologicalSpace (chapter04LocalField K v) := by
  cases v with
  | inl w =>
      change TopologicalSpace (Chapter04FiniteLocalField K w)
      infer_instance
  | inr w =>
      change TopologicalSpace w.Completion
      infer_instance

instance chapter04LocalFieldCommRing
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04Place K) : CommRing (chapter04LocalField K v) := by
  cases v with
  | inl w =>
      change CommRing (Chapter04FiniteLocalField K w)
      infer_instance
  | inr w =>
      change CommRing w.Completion
      infer_instance

def chapter04LocalIntegralSubring
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04Place K) : Subring (chapter04LocalField K v) :=
  match v with
  | Sum.inl w => (w.adicCompletionIntegers K).toSubring
  | Sum.inr _ => ⊤

def chapter04LocalIntegralSet
    (K : Type uK) [Field K] [NumberField K]
    (v : Chapter04Place K) : Set (chapter04LocalField K v) :=
  chapter04LocalIntegralSubring K v

abbrev Chapter04AllPlaceRestrictedProduct
    (K : Type uK) [Field K] [NumberField K] :=
  Πʳ v : Chapter04Place K,
    [chapter04LocalField K v, chapter04LocalIntegralSubring K v]_[Filter.cofinite]

def chapter04AdeleCoordinate
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (v : Chapter04Place K) : chapter04LocalField K v :=
  match v with
  | Sum.inl w => x.2 w
  | Sum.inr w => x.1 w

def chapter04FiniteAdeleCoordinate
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (v : Chapter04FinitePlace K) :
    Chapter04FiniteLocalField K v :=
  x.2 v

def chapter04InfiniteAdeleCoordinate
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (v : Chapter04InfinitePlace K) : v.Completion :=
  x.1 v

theorem chapter04_adelic_coordinate_finite
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (v : Chapter04FinitePlace K) :
    chapter04AdeleCoordinate K x (Sum.inl v) = x.2 v := by
  rfl

theorem chapter04_adelic_coordinate_infinite
    (K : Type uK) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (v : Chapter04InfinitePlace K) :
    chapter04AdeleCoordinate K x (Sum.inr v) = x.1 v := by
  rfl

@[ext]
theorem chapter04_adeleRing_ext
    (K : Type uK) [Field K] [NumberField K]
    {x y : Chapter04AdeleRing K}
    (hInf : x.1 = y.1) (hf : x.2 = y.2) :
    x = y := by
  exact Prod.ext hInf hf

end

end LastLib.Book04AdelesAndIdeles.Chapter04
